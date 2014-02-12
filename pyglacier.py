#!/usr/bin/env python

#
# pyglacier - Python tool to sync and manage data in Amazon Glacier
#
# Known "issues" to address:
#  - Glacier support only single write-once metadata field (archive description) per archive/file
#  - Archives are labeled with a server-generated random ID, not original filename
#  - Lookups are SLOW, on order of hours; involve submitting job request and polling for status
#
# Req's/functionality:
#  - Watch a folder and upload new/changed files automatically
#  - Optionally encrypt files
#  - Compute checksums and insert into archive description
#  - Keep track of archive ID's via extended attributes within filesystem; support secondary method using DB as well
#  - Periodically run verification proccess
#  - Modular?
#  - ...more to come...
#
#
# Watcher:
#  - Determine files that need to be synced:
#    - Find date of last execution
#    - Find files added/modified since last execution date
#    - =OR=
#    - Get directory listing
#    - Get fs/db listing
#    - Find files in dir but not fs/db
#


#
# filename, desc -> aws -> archive_id -> xattr
# desc: filename, hash, size
#


#
# Architecture design choices:
#  - Invocation style:
#    - Daemon / single-run via cron
#


import re
import os
import sys
import ast
import pdb
import xattr
import base64
import getopt
import string
import hashlib
import getpass
import time
import calendar
#from datetime import date, timedelta, datetime
from functools import partial

import ConfigParser

import sqlalchemy as sa

from Crypto.Cipher import AES
from Crypto.Util import Counter
from Crypto.Protocol.KDF import PBKDF2

from boto.glacier import exceptions as BotoExceptions
#from boto.glacier.job import Job as BotoJob
#from boto.glacier.vault import Vault as BotoVault
from boto.glacier.layer1 import Layer1 as BotoLayer1
from boto.glacier.layer2 import Layer2 as BotoLayer2
from boto.glacier.concurrent import ConcurrentUploader as BotoConcurrentUploader


GLACIER_UPLOAD = 1
GLACIER_LIST_JOBS = 2
GLACIER_JOB_INVENTORY = 3
GLACIER_JOB_DOWNLOAD = 4
GLACIER_JOB_OUTPUT_INVENTORY = 5
GLACIER_JOB_OUTPUT_DOWNLOAD = 6
GLACIER_ARCHIVE_REMOVE = 7
PYGLACIER_GEN_KEY = 8
PYGLACIER_ENCRYPT = 9
GLACIER_UNKNOWN = 0xFF



# http://code.activestate.com/recipes/410692/
class switch(object):
    def __init__(self, value):
        self.value = value
        self.fall = False

    def __iter__(self):
        """Return the match method once, then stop"""
        yield self.match
        raise StopIteration

    def match(self, *args):
        """Indicate whether or not to enter a case suite"""
        if self.fall or not args:
            return True
        elif self.value in args: # changed for v1.5, see below
            self.fall = True
            return True
        else:
            return False



def dict_pretty_print(self, data, key_map=[], key_order=[], width=22):
    str_rep = ""

    for item in data:
        # Iterate through keys in key_order; used to give priority of which
        # keys are displayed first
        for key in key_order:
            if key in key_map:
                key_str = key_map[key]
            elif len(str(key).translate(None, string.ascii_lowercase)) == 2:
                key_str = re.sub(r'(?<=.)([A-Z])', r' \1', key)
            else:
                key_str = key

            # Render our mapped key name + key data, append to string
            str_rep = "%s\t%*s : %s\n" % (str_rep, -1 * width, key_str, item[key])

        # Iterate through keys in data not covered previously
        for key in set(item.keys()) - set(key_order):
            if item[key] is None: continue          # Skip uninitialized data
            if key in key_map:
                key_str = key_map[key]
            elif len(str(key).translate(None, string.ascii_lowercase)) == 2:
                key_str = re.sub(r'(?<=.)([A-Z])', r' \1', key)
            else:
                key_str = key
            str_rep = "%s\t%*s : %s\n" % (str_rep, -1 * width, key_str, item[key])

    return str_rep


class BotoGlacierJobGeneric(object):
    #job_key_map = {'JobId': 'ID', 'VaultARN': 'Vault', 'JobDescription': 'Description', 'ArchiveId': 'Archive ID' }
    key_map = { 'RequestId': 'Request ID' }
    #key_order = [ 'RequestId' ]
    def __init__(self, data=None):
        #print "in __init__ %s , data=%s" % (self.__class__, data)
        if data is not None and 'RequestId' in data:
            self.request_id = data['RequestId']

    def __str__(self):
        return "%s, request ID: %s>" % (str(self.__class__)[:-1], self.request_id)

    def _keymap(self, key):
        if key in self.key_map:
            key_str = self.key_map[key]
        elif len(str(key).translate(None, string.ascii_lowercase)) <= 2:
            key_str = re.sub(r'(?<=.)([A-Z])', r'_\1', key).lower()
        else:
            key_str = key

        return key_str

    # This is where the magic happens
    def __build_class__(self, data):
        for k,v in data.items():
            key = self._keymap(k)
            #print "setting key %25s to %-25s = %s" % (k, key, v)
            setattr(self, key, v)




# Request sent to list jobs
# data from boto.glacier.layer1.list_jobs()
class BotoGlacierJobList(BotoGlacierJobGeneric):
    key_map = {'JobId': 'ID', 'VaultARN': 'vault', 'JobDescription': 'description', 'ArchiveId': 'archive_id' }
    #key_order = [ 'JobId', 'VaultARN', 'Action', 'JobDescription', 'StatusCode', 'StatusMessage', 'Completed', 'CreationDate', 'CompletionDate', 'InventorySizeInBytes' ]
    def __init__(self):
        self.job_list = []

    def __init__(self, data):
        self.job_list = []
        super(BotoGlacierJobList, self).__init__(data)
        for job in data['JobList']:
            new_job = BotoGlacierJobListJob(job)
            self.job_list.append(new_job)

    def __str__(self):
        str_rep = super(BotoGlacierJobList, self).__str__() + "\n"
#        str_rep += "<joblist>\n"
        for job in self.job_list:
            str_rep += "  %s\n" % job
#        str_rep += "</joblist>\n"
        return str_rep


# Job returned in JobList list from boto.glacier.layer1.list_jobs()
class BotoGlacierJobListJob(BotoGlacierJobGeneric):
    key_map = {'JobId':'job_id', 'VaultARN':'vault', 'JobDescription':'description', 'ArchiveId':'archive_id', 'InventorySizeInBytes':'inventory_size', 'ArchiveSizeInBytes':'archive_size', 'SNSTopic':'sns_topic', 'RetrievalByteRange':'retrieval_byte_range', 'SHA256TreeHash':'sha256_treehash', 'ArchiveSHA256TreeHash':'archive_sha256_treehash' }
    def __init__(self, data):
        super(BotoGlacierJobListJob, self).__init__()
        super(BotoGlacierJobListJob, self).__build_class__(data)

    def __str__(self):
        return "%s, job_id: %s, action: %s, creation: %s, status code: %s>" % (str(self.__class__)[:-1], self.job_id, self.action, self.creation_date, self.status_code)


# Either vault inventory or content of archive
class BotoGlacierJobOutput(BotoGlacierJobGeneric):
    def __init__(self):
        super(BotoGlacierJobOutput, self).__init__()
        self.job_type = None

    def __init__(self, data):
        super(BotoGlacierJobOutput, self).__init__(data)
        super(BotoGlacierJobOutput, self).__build_class__(data)
        if 'ArchiveList' in data.keys():
            self.job_type = GLACIER_JOB_INVENTORY
        elif 'ArchiveContents' in data.keys():
            self.job_Type = GLACIER_JOB_DOWNLOAD
        else:
            self.job_type = GLACIER_UNKNOWN

#        self.vault_arn = data['VaultARN']
#        self.content_type = data['ContentType']
#        self.content_range = data['ContentRange']
#        self.inventory_date = data['InventoryDate']

        if self.job_type == GLACIER_JOB_INVENTORY:
            self.archive_list = []

            for archive in data['ArchiveList']:
                new_archive = BotoGlacierArchiveItem(archive)
                self.archive_list.append(new_archive)
            #pdb.set_trace()

        else:
            print "[error] unknown job type: %s" % self.job_type

    # TODO: This needs to be fixed
    def __str__(self):
        str_rep = super(BotoGlacierJobOutput, self).__str__() + "\n"
        str_rep += "<archives>\n"
        for archive in self.archive_list:
            str_rep += "\t" + archive.__str__() + "\n"
        str_rep += "</archives>\n"
        return str_rep



class BotoGlacierArchiveItem(BotoGlacierJobGeneric):
    key_map = {'ArchiveDescription': 'archive_desc', 'SHA256TreeHash': 'sha256_treehash' }

    def __init__(self):
        self.archive_id = None
        self.archive_desc = None
        self.creation_date = None
        self.sha256_treehash = None
        self.mtime = 0
        self.size = 0

    # Archive description version revisions:
    # Unversioned = "size-mtime-sha256" (deprecated)
    # V01 = "V01|filename|mtime|utime|sha256"
    # V02 = "V02|b64-encoded-filename|mtime"
    #       - sha256/utime done by Glacier
    def __init__(self, data):
        self.archive_id = None
        self.archive_desc = None
        self.creation_date = None
        self.sha256_treehash = None
        self.mtime = 0
        self.size = 0
        self.filename = None

        super(BotoGlacierArchiveItem, self).__init__(data)
        super(BotoGlacierArchiveItem, self).__build_class__(data)

        metadata_ver = self.archive_desc[:3]
        if metadata_ver[0] == "V":
            self.metadata_ver = int(metadata_ver[1:3])
        else:
            self.metadata_ver = GLACIER_UNKNOWN

        if self.metadata_ver == GLACIER_UNKNOWN:
#            parsing = True
#            delim = 0
#            delim_chars = [ '|', '-' ]
#            while parsing:
#                if delim >= len(delim_chars):
#                    parsing = False
#                    continue
#                pygd = self.archive_desc.split(delim_chars[delim])
#                if len(pygd) == 1:
#                        delim += 1
#                        continue
#
#                #pygd = self.archive_desc.split("-")
                print "[error] unknown metadata version, contents: %s" % self.archive_desc
                pdb.set_trace()
#            #else:
#                self.filename = pygd[0]
#                self.mtime = int(pygd[1])
#                self.utime = int(pygd[2])
#                self.sha256_filehash = pygd[3]
#                #if not int(pygd[0]) == int(self.size):
#                #    print "[error] metadata corruption, size in Glacier (%d) and application metadata (%d) differ!" % (self.size, pygd[0])
        elif self.metadata_ver == 1:
            # Split when we know it's safe (ver detected)
            pygd = self.archive_desc.split("|")
            # Ver is pygd[0] though we extract as fixed length
            self.filename = pygd[1].replace('\\|', '|')
            self.mtime = int(pygd[2])
            self.utime = int(pygd[3])
            self.sha256_filehash = pygd[4]
        elif self.metadata_ver == 2:
            # Split when we know it's safe (ver detected)
            pygd = self.archive_desc.split("|")
            # Ver is pygd[0] though we extract as fixed length
            self.filename = base64.b64decode(pygd[1])
            self.mtime = int(pygd[2])
            #self.utime = int(pygd[3])
            #self.sha256_filehash = pygd[4]
        else:
            print "[error] unknown metadata version!"

    def __str__(self):
        #return "%s, version: %d, size: %s, creation_date: %s, mtime: %d, archive_id: %s, archive_desc: %s>" % (str(self.__class__)[:-1], self.metadata_ver, self.size, self.creation_date, self.mtime, self.archive_id, self.archive_desc)
        return "%s, version: %d, filename: %s, size: %s, creation_date: %s, archive_id: %s, archive_desc: %s>" % (str(self.__class__)[:-1], self.metadata_ver, self.filename, self.size, self.creation_date, self.archive_id, self.archive_desc)




class PyGlacier:
    """ do stuff """

    def __init__(self):
        self.dryrun = False
        self.recursive = False
        self.op = GLACIER_UPLOAD
        # parse command line options
        try:
            opts, args = getopt.getopt(sys.argv[1:], "hgenR:up:lq:rid:v:w:", ["help", "--generate-key", "path", "list-jobs", "query-job", "download", "remove", "inventory"])
        except getopt.error, msg:
            print msg
            print "for help use --help"
            sys.exit(2)
        # process options
        for o, a in opts:
            if o in ("-h", "--help"):
                print __doc__
                sys.exit(0)
            if o in ("-g", "--generate-key"):
                self.op = PYGLACIER_GEN_KEY
            if o in ("-e", "--encrypt"):
                self.op = PYGLACIER_ENCRYPT
            if o in ("-p", "--path"):
                self.path = a
            if o in ("-r", "--recursive"):
                self.recursive = True
            if o in ("-n", "--dry-run"):
                self.dryrun = True
            if o in ("-l", "--list-jobs"):
                self.op = GLACIER_LIST_JOBS
            if o in ("-i", "--inventory-job"):
                self.op = GLACIER_JOB_INVENTORY
            if o in ("-d", "--download-job"):
                self.op = GLACIER_JOB_DOWNLOAD
                self.archive_id = a
            if o in ("-v", "--output-inVentory"):
                self.op = GLACIER_JOB_OUTPUT_INVENTORY
                self.jobid = a
            if o in ("-w", "--output-doWnload"):
                self.op = GLACIER_JOB_OUTPUT_DOWNLOAD
                self.jobid = a
            if o in ("-R", "--Remove"):
                self.op = GLACIER_ARCHIVE_REMOVE
                self.archive_id = a
    #    # process arguments
    #    for arg in args:
    #        process(arg) # process() is defined elsewhere
        self.start_time = int(time.time())


    def run(self):
        # Determine our platform
        self.uname = os.uname()

        # Get last execution date and listing of files
        config = ConfigParser.RawConfigParser()
        config.read(['pyglacier.conf', os.path.expanduser('~/.pyglacier.conf')])
        self.config = config
        self.encrypt = config.get('options', 'encrypt')
        #self.read_config()
        self.boto_glacier = GlacierInterface(self.config)


        # Connect to DB
        self.db = sa.create_engine('sqlite:///pyglacier.db')
        self.metadata = sa.MetaData(self.db)
        try:
            self.files_table = sa.Table('files', self.metadata, autoload='True')
        except sa.exc.NoSuchTableError:
            print "[warning] files table missing, creating"
            self.files_table = sa.Table('files', self.metadata,
                #sa.Column('id',sa.Integer,primary_key=True),
                sa.Column('archiveid',sa.String(255),primary_key=True),
                sa.Column('filename',sa.String(255),nullable=False),
                sa.Column('utime',sa.Integer),
                sa.Column('mtime',sa.Integer),
                sa.Column('sha256',sa.String(64))
            )
            self.metadata.create_all()

        if self.op == GLACIER_UPLOAD:
            self.upload()
        elif self.op == GLACIER_LIST_JOBS:
            self.list_jobs()
        elif self.op == GLACIER_JOB_INVENTORY:
            self.job_start_inventory()
        elif self.op == GLACIER_JOB_DOWNLOAD:
            self.job_start_download(self.archive_id)
        elif self.op == GLACIER_JOB_OUTPUT_INVENTORY:
            self.job_output_inventory(self.jobid)
        elif self.op == GLACIER_JOB_OUTPUT_DOWNLOAD:
            self.job_output_download(self.jobid)
        elif self.op == GLACIER_ARCHIVE_REMOVE:
            self.archive_remove(self.archive_id)
        elif self.op == PYGLACIER_GEN_KEY:
            print "key: %s" % self.generate_key().encode('hex')


    def treehash_sha256(self, filename):
        if not os.path.isfile(filename): return None
        with open(filename, mode='rb') as f:
            h = hashlib.sha256()
            size = os.path.getsize(filename)

            # Calculate 1mb hashes
            hashes = []
            offset = 0
            while offset < size:
                hashes.append(self.treehash_sha256_1mb(f, offset))
                offset += 1<<20
            #print hashes

            # Hash and reduce
            index = 0
            while True:
                pos = 0
                while pos+2**index < len(hashes):
                    h.update(hashes[pos])
                    h.update(hashes[pos+2**index])
                    for i in range(pos+1, pos+2**index+1):
                        hashes[i] = None
                    hashes[pos] = h.hexdigest()
                    h = hashlib.sha256()
                    pos += 2**(index+1)

                #print hashes
                index += 1
                if len(hashes) <= 2**index:
                    break

        return hashes[0]


    def treehash_sha256_1mb(self, handle, position):
        if position % (1<<20) != 0:
            print "[error] treehash_sha256_1mb position %d not aligned!" % position
            return None

        h = hashlib.sha256()
        handle.seek(position)

        for b in iter(partial(handle.read, 256), b''):
            #print handle.tell()
            h.update(b)
            if handle.tell()+256 > position+1<<20:
                break

        return h.hexdigest()


    def sha256(self, filename):
        return self.fullhash_sha256(filename)

    def fullhash_sha256(self, filename):
        if not os.path.isfile(filename): return None
        with open(filename, mode='rb') as f:
            h = hashlib.sha256()
            for b in iter(partial(f.read, 256), b''):
                h.update(b)
        return h.hexdigest()


    def md5(self, filename):
        if not os.path.isfile(filename): return None
        with open(filename, mode='rb') as f:
            h = hashlib.md5()
            for b in iter(partial(f.read, 128), b''):
                h.update(b)
        return h.hexdigest


    def generate_key(self):
        passphrase = getpass.getpass("Passphrase: ")
        salt = os.urandom(32)
        key = PBKDF2(passphrase, salt, dkLen=32, count=20000)
        return key


    def encrypt(self, key, plaintext):
        #key = self.generate_key()
        iv = os.urandom(32)
        #counter = Crypto.Util.Counter.new(128, initial_value=long(iv.encode("hex"), 16))
        counter = Counter.new(128, initial_value=long(iv.encode("hex"), 16))
        cipher = AES.new(key, AES.MODE_CTR, counter=counter)
        ciphertext = cipher.encrypt(plaintext)
        print ciphertext



    def get_xattrs(self, filename):
        if not os.path.isfile(filename): return None
        x = xattr.xattr(filename)
        return x


    def set_xattr(self, filename, key, value):
        if not os.path.isfile(filename): return None
        x = xattr.xattr(filename)
        x[key] = value


    def read_config(self, debug=False):
        """ Read config file """
        config = ConfigParser.RawConfigParser()

        config.read(['pyglacier.conf', os.path.expanduser('~/.pyglacier.conf')])
        self.config = config
        self.encrypt = config.get('options', 'encrypt')


    def get_last_run(self, debug=False):
        """ Get timestamp of last execution """
        lastrun = time.localtime(int(self.config.get('log', 'last_run')))
        return lastrun


    def find_files(self, lastrun, debug=False):
        """ Find modified files to upload """
        try:
            dirlist = os.listdir(self.path)
        except OSError:
            print "[error] unable to open path %s" % path

        newfiles = []
        dirlist.sort()

        while dirlist:
            file = dirlist.pop()
            filename = os.path.join(self.path, file)

            if os.path.isdir(filename):
                for subfile in os.listdir(filename):
                    dirlist.append(os.path.join(file, subfile))
                continue
            if os.path.islink(filename) and not os.path.exists(filename):
                print "[error] broken symbolic link %s" % filename
                continue

            try:
                e_mtime = os.path.getmtime(filename)
            except OSError:
                print "[error] unable to get mtime on %s" % file
                e_mtime = 0

            l_mtime = time.localtime(e_mtime)
            size = os.path.getsize(filename)

            if debug: print file, l_mtime, lastrun
            newfile = {}
            newfile['name'] = file
            newfile['abspath'] = os.path.join(self.path, file)
            newfile['mtime'] = l_mtime
            newfile['size'] = size
            newfile['xattr'] = self.get_xattrs(newfile['abspath'])
            if l_mtime > lastrun:
                newfile['upload'] = True
            else:
                newfile['upload'] = False
            newfiles.append(newfile)

        return newfiles


    def upload(self):
        """ Create an archive / upload file """
        #print lastrun
        lastrun = self.get_last_run()
        files = self.find_files(lastrun)
        uploadfiles = [ f for f in files if f['upload'] ]
        uploadsize = sum( f['size'] for f in uploadfiles )
        print "using path %s, %d/%d files to upload (%d kb)\n" % (self.path, len(uploadfiles), len(files), uploadsize>>10)

        # Compute hashes
        for f in uploadfiles:
            ##f['sha256'] = "0xDEADBEEF"
            ##f['sha256'] = self.sha256(f['abspath'])
            #f['sha256'] = "[.             ]"
            #print "%s  %6d kb  %s  %s" % (time.strftime("%c", f['mtime']), f['size']>>10, f['sha256'][:16], f['name'])
            f['sha256'] = self.treehash_sha256(f['abspath'])
            print "%s  %6d kb  %s  %s" % (time.strftime("%c", f['mtime']), f['size']>>10, f['sha256'][:16], f['name'])
            ##print "%s  %6d kb  %s  %s" % (time.strftime("%c", f['mtime']), f['size']>>10, f['sha256'][:16], self.sha256(f['abspath'])[:16], f['name'])

        #pdb.set_trace()

        for f in uploadfiles:
            ans = raw_input("Upload file %s? (y/n/q): " % f['name'])
            if ans == 'q': break
            elif ans != 'y': continue

            #archive_desc = "%d-%d-%d-%s" % (f['size'], calendar.timegm(f['mtime']), self.start_time, f['sha256'])
            archive_desc = "V02|%s|%d|%d|%s" % (base64.b64encode(f['name']), calendar.timegm(f['mtime']), self.start_time, f['sha256'])
            #archive_desc = "V01|%s|%d|%d|%s" % (f['name'].replace('|', '\\|'), calendar.timegm(f['mtime']), self.start_time, f['sha256'])
            print "using archive description: %s" % archive_desc
            archive_id = "0xDEADC0DE"
            print "starting upload...";
            pdb.set_trace()
            archive_id = self.boto_glacier.aws_create_archive(f['abspath'], archive_desc)
            print "upload finished, archive ID: %s" % archive_id

            try:
                self.set_xattr(f['abspath'], 'pyglacier-archiveid', "%s" % archive_id)
                self.set_xattr(f['abspath'], 'pyglacier-utime', "%s" % self.start_time)
            except IOError:
                print "[error] unable to set xattr on file %s" % f['abspath']

            i = self.files_table.insert()
            try:
                i.execute(filename=f['name'],archiveid=archive_id,utime=self.start_time,mtime=calendar.timegm(f['mtime']),sha256=f['sha256'])
            except sa.exc.SQLAlchemyError:
                print "[error] unable to add filename \"%s\" to database" % f['name']

        # Update our config file to reflect last execution timestamp
        if not self.config.has_section('log'):
            self.config.add_section('log')
        now = time.mktime(time.localtime(self.start_time))
        #print self.start_time, now
        self.config.set('log', 'last_run', int(now))
        if not self.dryrun:
            with open('pyglacier.conf', 'wb') as configfile:
                self.config.write(configfile)


    def print_val(self, format, value):
        if value is not None:
            print format % value


    def pretty_print(self, key_map, key_order, data, width=22):
        for item in data:
            for key in key_order:
                if key in key_map:
                    key_str = key_map[key]
                elif len(str(key).translate(None, string.ascii_lowercase)) == 2:
                    key_str = re.sub(r'(?<=.)([A-Z])', r' \1', key)
                else:
                    key_str = key
                print "\t%*s : %s" % (-1 * width, key_str, item[key])

            for key in set(item.keys()) - set(key_order):
                if item[key] is None: continue
                if key in key_map:
                    key_str = key_map[key]
                elif len(str(key).translate(None, string.ascii_lowercase)) == 2:
                    key_str = re.sub(r'(?<=.)([A-Z])', r' \1', key)
                else:
                    key_str = key
                print "\t%*s : %s" % (-1 * width, key_str, item[key])


    def list_jobs(self):
        """ List jobs on vault """
        DISP_JOB_WIDTH = 22
        job_key_map = {'JobId': 'ID', 'VaultARN': 'Vault', 'JobDescription': 'Description', 'ArchiveId': 'Archive ID' }
        job_key_order = [ 'JobId', 'VaultARN', 'Action', 'JobDescription', 'StatusCode', 'StatusMessage', 'Completed', 'CreationDate', 'CompletionDate', 'InventorySizeInBytes' ]
        print "querying job listing..."
        jobs = self.boto_glacier.aws_list_jobs()

        ###
#        cl_job = BotoGlacierJobGeneric(jobs)
#        print "Python class 1:",cl_job

        cl2_job = BotoGlacierJobList(jobs)
        print "Python class:\n", cl2_job
        ###

        print "debug:"
        print "jobs: ", jobs
        self.pretty_print(job_key_map, job_key_order, jobs['JobList'], DISP_JOB_WIDTH)


    def archive_remove(self, archive_id):
        """ Remove an archive """
        print "submitting job request to delete archive ID %s" % archive_id
        result = self.boto_glacier.aws_delete_archive(archive_id)
        print result


    def job_start_inventory(self):
        """ Submit job for archive inventory of vault """
        print "submitting job inventory request..."
        list_job = self.boto_glacier.aws_job_start_inventory()
        print "inventory job:", list_job


    def job_start_download(self, archive_id):
        """ Submit job for archive retrieval """
        print "submitting job request to download archive ID %s" % archive_id
        download_job = self.boto_glacier.aws_job_start_download(archive_id)
        print "download job:", download_job


    def job_output_inventory(self, jobid):
        """ Retrieve output of vault inventory job """
        DISP_JOB_WIDTH = 22
        archive_key_map = {'ArchiveId': 'ID', 'ArchiveDescription': 'Description' }
        archive_key_order = [ 'ArchiveId', 'ArchiveDescription', 'CreationDate', 'Size' ]
        print "querying inventory job status..."
        try:
            job_status = self.boto_glacier.aws_job_output_inventory(jobid)
        except BotoExceptions.UnexpectedHTTPResponseError as e:
            body = ast.literal_eval(e.body)         # safe eval()
            if e.status == 400 and body['message'].startswith("The job is not currently available for download"):
                print "[error] job not completed, unavailable for download, aborting"
                return
            elif e.status == 404 and body['message'].startswith("The job ID was not found"):
                print "[error] job ID not found, aborting"
                return
            else:
                print "[error] unexpected HTTP response header exception caught!"
                print e
                pass
        except:
            raise
            import pdb
            pdb.set_trace()
            return

        ###
        cl_job_status = BotoGlacierJobOutput(job_status)
        print "Python object:\n", cl_job_status
        ###

        print "debug:\n"
        print "job_status: ", job_status
        self.pretty_print(archive_key_map, archive_key_order, job_status['ArchiveList'], DISP_JOB_WIDTH)


    def job_output_download(self, jobid):
        """ Retrieve output of archive retrieval job / download archive contents """
        print "querying download job status..."
        try:
            job_status = self.boto_glacier.aws_job_output_download(jobid, (0,1023))
        except BotoExceptions.UnexpectedHTTPResponseError as e:
            body = ast.literal_eval(e.body)         # safe eval()
            if e.status == 400 and body['message'].startswith("The job is not currently available for download"):
                print "[error] job not completed, unavailable for download, aborting"
                return
            elif e.status == 404 and body['message'].startswith("The job ID was not found"):
                print "[error] job ID not found, aborting"
                return
            else:
                print "[error] unexpected HTTP response header exception caught!"
                print e
                pass
        except:
            raise
            import pdb
            pdb.set_trace()
            return

        print "job_status: ", job_status



class DataInterface():
    def __init__(self, filename):
        self.filename = filename
        self.file = open(self.filename, 'rb')

    def read_1mb(self):
        return None



class GlacierInterface():
    def __init__(self, config):
        self.aws_access = config.get('auth_dir1', 'aws_access')
        self.aws_secret = config.get('auth_dir1', 'aws_secret')
        self.vault_name = config.get('auth_dir1', 'vault_name')
#        pdb.set_trace()
        if not hasattr(self,'path'):
            self.path = config.get('auth_dir1', 'path')
        self.boto_glacier_l1 = BotoLayer1(aws_access_key_id=self.aws_access, aws_secret_access_key=self.aws_secret)
        self.boto_glacier_l2 = BotoLayer2(aws_access_key_id=self.aws_access, aws_secret_access_key=self.aws_secret)


    def aws_create_archive(self, file, description):
        aws_uploader = BotoConcurrentUploader(self.boto_glacier_l1, self.vault_name, 32*1<<20)
        archive_id = aws_uploader.upload(file, description)
        return archive_id


    def aws_delete_archive(self, archive_id):
        return self.boto_glacier_l1.delete_archive(self.vault_name, archive_id)


    def aws_list_jobs(self):
        #job_list = self.boto_glacier_l1.list_jobs(self.vault_name, completed=False)
        job_list = self.boto_glacier_l1.list_jobs(self.vault_name)
        return job_list


    def aws_job_start_download(self, archive_id):
        job_id = self.boto_glacier_l1.initiate_job(self.vault_name, { "Description":"download-job", "Type":"archive-retrieval", "ArchiveId":"%s" % archive_id })
        return job_id


    def aws_job_start_inventory(self):
        job_id = self.boto_glacier_l1.initiate_job(self.vault_name, { "Description":"inventory-job", "Type":"inventory-retrieval", "Format":"JSON" })
        return job_id


    def aws_job_output_inventory(self, jobid):
        job_output = self.boto_glacier_l1.get_job_output(self.vault_name, jobid)
        return job_output


    def aws_job_output_download(self, jobid, range=None):
        vault = self.boto_glacier_l2.get_vault(self.vault_name)
        job = vault.get_job(jobid)
        job.download_to_file("testfile")
        print job



def main():
    pyglacier = PyGlacier()
    pyglacier.run()


if __name__ == "__main__":
    main()





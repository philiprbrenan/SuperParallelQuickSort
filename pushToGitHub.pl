#!/usr/bin/perl -I/home/phil/perl/cpan/DataTableText/lib/ -I/home/phil/perl/cpan/GitHubCrud/lib/
#-------------------------------------------------------------------------------
# Push QSP code to GitHub
# Philip R Brenan at gmail dot com, Appa Apps Ltd Inc., 2022
#-------------------------------------------------------------------------------
use warnings FATAL => qw(all);
use strict;
use Carp;
use Data::Dump qw(dump);
use Data::Table::Text qw(:all);
use GitHub::Crud qw(:all);
use feature qw(say current_sub);

my $home = q(/home/phil/people/Jocelyn/quickSort/perl/);                        # Local files
my $user = q(philiprbrenan);                                                    # User
my $repo = q(SuperParallelQuickSort);                                           # Store code here so it can be referenced from a browser
my $wf   = q(.github/workflows/main.yml);                                       # Work flow on Ubuntu

expandWellKnownWordsInMarkDownFile                                              # Documentation
  fpe($home, qw(README md2)), fpe $home, qw(README md);

push my @files, searchDirectoryTreesForMatchingFiles($home, qw(.md .pl));      # Files

for my $s(@files)                                                               # Upload each selected file
 {my $p = readFile($s);                                                         # Load file
  my $t = swapFilePrefix $s, $home;
  next if $s =~ m(/backups/);                                                   # Ignore this folder
  my $w = writeFileUsingSavedToken($user, $repo, $t, $p);
  lll "$w $s $t";
 }

my $d = dateTimeStamp;

my $y = <<'END';
# Test $d

name: Test

on:
  push

jobs:
  test:
    runs-on: ubuntu-latest

    steps:
    - uses: actions/checkout@v2
      with:
        ref: 'main'

    - name: Cpan
      run: |
        sudo cpan install -T Data::Dump Data::Table::Text

    - name: Super Parallel QuickSort
      run: |
        perl qsp.pl
END

lll "Ubuntu work flow for $repo ", writeFileUsingSavedToken($user, $repo, $wf, $y);

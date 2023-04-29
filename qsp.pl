#!/usr/bin/perl -I/home/phil/perl/cpan/DataTableText/lib/
#-------------------------------------------------------------------------------
# Super parallel quick sort
# Philip R Brenan at appaapps dot com, Appa Apps Ltd Inc., 2023
#-------------------------------------------------------------------------------
use v5.30;
use warnings FATAL => qw(all);
use strict;
use Carp;
use Data::Dump qw(dump);
use Data::Table::Text qw(:all);
use Time::HiRes qw(time);
use Test::More tests=>32;

makeDieConfess;

my $home   = currentDirectory;                                                  # Home folder
my $save   = fpd $home, qw(save);                                               # Save files her
my $output = fpe $home, qw(output txt);                                         # Output file
#              0 1 2 3 4 5 6 7 8  9 10 11
my @array = qw(4 6 3 2 1 5 9 7 8 12 11 10);                                     # Sample array to sort
#                  ---------
#               0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
my @array2 = qw(4  6  3  2  1  5  9  7  8 12 11 10  4  6  3  2  1  5  9  7  8 12 11 10  3  2  1  5  9  7  8 12);                                     # Sample array to sort
#               ----------------------  4+4++4++4+++4++4++0++0

eval {goto latest};

sub printArray($$)                                                              # Print an array
 {my ($title, $array) = @_;                                                     # Title, array
  my @s;
  push @s, "$title: ";
  for my $i(0..$#$array)
   {if (defined $$array[$i])
     {push @s, sprintf("%4d,",  $$array[$i]);
     }
    else
     {push @s, sprintf("undef");
     }
   }
  push @s, "\n";
  join " ", @s;
 }

sub checkArray($)                                                               # Check an array has been sorted
 {my ($array) = @_;                                                             # Array
  for my $i(1..$#$array)
   {confess "Not sorted at $i" if $$array[$i] <$$array[$i-1];
   }
  1
 }

sub createArray($)                                                              # Check an array has been sorted
 {my ($N) = @_;                                                                 # Size of array
  my @a;
  srand(1);
  push @a, rand() for 1..$N;
  [@a]
 }

sub timeTask(&)                                                                 # Return the number of secods a task took
 {my ($task) = @_;                                                                 # Size of array
  my $s = time;
  &$task;
  time - $s
 }

sub classify($)                                                                 # Classify an array section by describing it as a set of lower elements and a set of upper elements
 {my ($section) = @_;                                                           # Section description

  my $start = $$section[0];
  my $end   = $$section[1];
  my $array = $$section[2];
  my $pivot = $$section[3];

  my @cl; my @ch; my $sl = 0; my $sh = 0;
  for my $i($$section[0]..$$section[1])                                         # Classify each element in the section
   {if ($$array[$i] < $pivot) {push @cl, ++$sl; push @ch, 0}
    else                      {push @ch, ++$sh; push @cl, 0}
   }

#        0         1       2    3     4    5
  bless [$section, $pivot, $sl, \@cl, $sh, \@ch], 'Section';                    # Section plus classification
 }

sub extendTree($)                                                               # Extend tree up
 {my ($tree) = @_;                                                              # Tree

  my @e = $tree;                                                                # Extended tree
  for   my $i(0..@$tree-2)                                                      # Each layer
   {my @l;
    my @r = $e[-1]->@*;
    while(@r > 1)
     {my $a = shift @r; my $b = shift @r;
      push @l, $a+$b;
     }
    push @l, @r;
    push @e, \@l;
   }
  \@e;
 }

sub tree($)                                                                     # Build tree sum from array sections
 {my ($sections) = @_;                                                          # Section description

  my @treeL; my @treeH;
  for my $s(@$sections)                                                         # Sections
   {ref($s) =~ m(Section)i or confess "Not a section";
    push @treeL, $$s[2];
    push @treeH, $$s[4];
   }

  [extendTree(\@treeL), extendTree(\@treeH)];
 }

sub positionSection($$)                                                         # Use a tree sum to locate the final position of a section
 {my ($tree, $section) = @_;                                                    # Tree sum, section number in tree

  my $p = $section; my $sum = 0;                                                # Section of array indexes the start node in the prefix sum tree
  for(my $t = 0; $t < $#$tree and $p > 0; ++$t)                                 # Go up the prefix sum tree
   {$sum += $$tree[$t][$p-1] if $p % 2 == 1;                                    # Turning left in section tree so need to add sibling amount
    $p >>= 1;                                                                   # Next layer of prefix sum tree
   }
  $sum
 }

sub placeSection($$$$$$)                                                        # Place the elements of a sectionion the output area based on their tree sum
 {my ($tree, $section, $sectionNumber, $out, $Start, $End) = @_;                # Tree sum, section, section number in tree, output area

  my $tL = $$tree[0];                                                           # Start of section in underlying array
  my $tH = $$tree[1];                                                           # End of section

  my $lS = $$section[0][0];                                                     # Start of section in underlying array
  my $hS = $$section[0][1];                                                     # End of section
  my $ar = $$section[0][2];                                                     # Underlying array
  my $pi = $$section[1];                                                        # Pivot
  my $lW = $$section[2];                                                        # Elements lower than pivot
  my $lP = $$section[3];                                                        # Lower element positions
  my $hW = $$section[4];                                                        # Elements greater than or equal to the pivot
  my $hP = $$section[5];                                                        # Higher element positions

  my $sl = positionSection($tL, $sectionNumber);                                # Place lower elements

  my @updates;                                                                  # Record any changes made

  for my $l(keys @$lP)
   {next unless my $p = $$lP[$l];
    my $o = $Start+$sl+$p-1;
    confess "Too big" if $o > $#$ar;
    confess "Too big" if $lS+$l > $#$ar;
    $$out[$o] = $$ar[$lS+$l];
    push @updates, [$o, $$out[$o]];                                             # Record change
   }

  my $sh  = positionSection($tH, $sectionNumber);                               # Place higher elements
  my $wl  = $$tL[-1][0];                                                        # Width of lower partition
  my $off = $Start+$wl + $sh - 1;                                               # Start of upper section

  for my $h(keys @$hP)
   {next unless my $p = $$hP[$h];
    my $o = $off+$p;
    confess "Too big" if $o > $#$ar;
    confess "Too big" if $lS+$h > $#$ar;
    $$out[$o] = $$ar[$lS+$h];
    push @updates, [$o, $$out[$o]];                                             # Record change
   }
  [@updates]
 }

sub placeElements($$$$$$)                                                       # Place elements in output area based on their prefix sum
 {my ($array, $width, $out, $Start, $End, $nThreads) = @_;                      # Parameters, start and end positions in the array

  my @s;
  my $range = $End - $Start + 1;
  my $span  = int($range / $width);                                             # Width chosen to be one or more
  ++$span while $span * $width < $range;

  my $pivot = $$array[$Start];                                                  # Choose pivot
  defined($pivot) or confess "Pivot undefined at $Start ".dump($array);

  for my $i(0..$span-1)                                                         # Each span of the specified width
   {my $start = $Start+$width*$i;                                               # Inclusive start
    my $end   = min($start+$width-1, min($End, $#$array));                      # Inclusive end
    push @s, classify([$start, $end, $array, $pivot]);                          # Classsif y each element as being bigger or smaller than the pivot
   }
  defined($pivot) or confess "Pivot undefined";

  my $t = tree(\@s);                                                            # Prefix sum tree
  defined($pivot) or confess "Pivot undefined";

  if ($nThreads >= 0)
   {for my $i(0..$#s)                                                           # Place each section
     {my $u = placeSection($t, $s[$i], $i, $out, $Start, $End);
     }
   }
  else
   {runInParallel -$nThreads, sub                                               # Copy back in parallel
     {my ($i) = @_;
      placeSection($t, $s[$i], $i, $out, $Start, $End);
     },
    sub                                                                         # Consolidate
     {for my $U(@_)
       {for my $u(@$U)
         {my ($i, $v) = @$u;
          $$out[$i] = $v;
         }
       }
     },
    0..$#s
   }
  defined($pivot) or confess "Pivot undefined";

  my $pivotIndex = $Start + $$t[0][-1][0];                                      # Location of pivot
  $$out[$pivotIndex] == $pivot or confess printArray("Pivot $pivot gone in", $out);

  my $w = 1+int(($End - $Start) / abs($nThreads));

  if ($nThreads >= 0)
   {for my $i(0..abs($nThreads))                                                # Reload array sequentially
     {my $s = $Start+$i * $w;
      my $e = min($s+$w, $End, @$array-1);
      for my $j($s..$e)
       {$$array[$j] = $$out[$j];
       }
     }
   }
  else
   {runInParallel -$nThreads, sub                                               # Copy back in parallel
     {my ($i) = @_;
      my $s = $Start+$i * $w;
      my $e = min($s+$w-1, $End, @$array-1);
      my @updates;
      for my $j($s..$e)
       {push @updates, [$j, $$out[$j]];
       }
      [@updates]
     },
    sub                                                                         # Consolidate
     {for my $U(@_)
       {for my $u(@$U)
         {my ($i, $v) = @$u;
          $$array[$i] = $v;
         }
       }
     },
    0..abs($nThreads);
   }

  $pivotIndex;
 }
sub qsSortPartition($$$$$)                                                      # Sort a partition
 {my ($array, $out, $Start, $End, $nThreads) = @_;                              # Array to sort, work area, start index, inclusive end index, number of threads
  return if $Start >= $End;                                                     # Inclusive at each end

  my $w = int(($End - $Start)/ abs($nThreads)); $w = 1 if $w < 1;               # Width of sort
  if ($w < 4)                                                                   # Too narrow
   {my @a = sort {$a <=> $b} map {$$array[$_]} $Start..$End;                    # Sort sub section
    $$array[$_] = $a[$_-$Start] for $Start..$End;                               # Reload array
    return;
   }
  my $p = placeElements($array, $w, $out, $Start, $End, $nThreads);             # Pivot partition

  __SUB__->($array, $out, $Start, $p-1, $nThreads);
  __SUB__->($array, $out, $p+1,   $End, $nThreads);
 }

# Sequential quicksort
sub qs($$)                                                                      # Sort an array
 {my ($nThreads, $array) = @_;                                                  # Threads, Array to sort

  my $o = [((undef) x scalar(@$array))];

  qsSortPartition($array, $o, 0, $#$o, $nThreads);
  $array
 }

# Tests
if (1)
 {my @o; @o = ((undef) x scalar(@array2));
  my $p = placeElements(\@array2, 8, \@o, 0, $#o, 1);
  ok $p == 9;
  is_deeply \@o, [3, 2, 1, 3, 2, 1, 3, 2, 1, 4, 6, 5, 9, 7, 8, 12, 11, 10, 4, 6, 5, 9, 7, 8, 12, 11, 10, 5, 9, 7, 8, 12];
 }

if (1)
 {my $x = [[qw(0 0 1 0 1)], [qw(0 0 1 0 1)], [qw(0 0 2 0 2)], [qw(0 0 3 0 3)], [qw(0 0 1 0 1)]];
  bless $_, "Section" for @$x;
  my $X = tree($x);

  is_deeply $X, [
    [[1, 1, 2, 3, 1], [2, 5, 1], [7, 1], [8], [8]],
    [[1, 1, 2, 3, 1], [2, 5, 1], [7, 1], [8], [8]]];
 }

if (1)
 {my $x = classify [2, 6, [@array], 4];
  is_deeply $x,
[[2, 6, [4, 6, 3, 2, 1, 5, 9, 7, 8, 12, 11, 10], 4],
  4,
  3,
  [1, 2, 3, 0, 0],
  2,
  [0, 0, 0, 1, 2]];
 }

if (1)
 {my @l = qw(1 1 2 3 1);
  my $l = extendTree(\@l);
  is_deeply $l, [[1, 1, 2, 3, 1], [2, 5, 1], [7, 1], [8], [8]];
 }

if (1)
 {my $x = classify [0, 7, [@array2], 4];
  is_deeply $$x[3], [1 .. 8];
  is_deeply $$x[5], [(0) x 8];
 }

if (1)
 {my $x = classify [8, 15, [@array2], 8];
  is_deeply $$x[3], [1 .. 4, 0, 5, 0, 0];
  is_deeply $$x[5], [0, 0, 0, 0, 1, 0, 2, 3];
 }

if (1)
 {my $tree =   [[1, 1, 2, 3, 1], [2, 5, 1], [7, 1], [8], [8]];
  is_deeply positionSection($tree, 0), 0;
  is_deeply positionSection($tree, 1), 1;
  is_deeply positionSection($tree, 2), 2;
  is_deeply positionSection($tree, 3), 4;
  is_deeply positionSection($tree, 4), 7;
  is_deeply positionSection($tree, 5), 8;
 }

if (1)
 {my $t = tree
   [classify([ 0,  7, [@array2], 4]),
    classify([ 8, 15, [@array2], 4]),
    classify([16, 23, [@array2], 4]),
    classify([24, 31, [@array2], 4]),
   ];

  is_deeply $t,
[[[8, 1, 0, 0], [9, 0],   [9], [9]],
 [[0, 7, 8, 8], [7, 16], [23], [23]]];
 }

#latest:;
is_deeply qs( 2, [6, 3, 2, 1, 4, 5, 9, 7, 8, 12, 11, 10]), [1..12];
is_deeply qs( 3, [6, 3, 2, 1, 4, 5, 9, 7, 8, 12, 11, 10]), [1..12];
is_deeply qs( 4, [6, 3, 2, 1, 4, 5, 9, 7, 8, 12, 11, 10]), [1..12];
is_deeply qs( 5, [6, 3, 2, 1, 4, 5, 9, 7, 8, 12, 11, 10]), [1..12];
is_deeply qs( 6, [6, 3, 2, 1, 4, 5, 9, 7, 8, 12, 11, 10]), [1..12];
is_deeply qs( 7, [6, 3, 2, 1, 4, 5, 9, 7, 8, 12, 11, 10]), [1..12];
is_deeply qs( 8, [6, 3, 2, 1, 4, 5, 9, 7, 8, 12, 11, 10]), [1..12];
is_deeply qs( 9, [6, 3, 2, 1, 4, 5, 9, 7, 8, 12, 11, 10]), [1..12];
is_deeply qs(10, [6, 3, 2, 1, 4, 5, 9, 7, 8, 12, 11, 10]), [1..12];
is_deeply qs(11, [6, 3, 2, 1, 4, 5, 9, 7, 8, 12, 11, 10]), [1..12];
is_deeply qs(12, [6, 3, 2, 1, 4, 5, 9, 7, 8, 12, 11, 10]), [1..12];
is_deeply qs(13, [6, 3, 2, 1, 4, 5, 9, 7, 8, 12, 11, 10]), [1..12];

is_deeply qs(2, [3, 2, 112, 10, 14, 15, 17, 18, 21]), [2, 3, 10, 14, 15, 17, 18, 21, 112];

#latest:;
is_deeply qs(2, [6, 3, 2, 1, 4, 5, 9, 7, 8, 11, 10, 23, 16, 13, 12, 14, 15, 19, 17, 18, 21, 20, 22]), [1..23];
is_deeply qs(2, [6, 3, 2, 24, 1, 4, 29, 5, 9, 7, 8, 11, 28, 30, 10, 23, 16, 27, 25, 13, 12, 14, 15, 19, 26, 17, 18, 21, 20, 22]), [1..30];

ok checkArray qs 5, createArray 100;

#latest:;
for my $nThreads(2..12)
 {say STDERR sprintf "Threads: %2d  Time : %8.4f", $nThreads,  timeTask {qs -$nThreads, createArray 1e2};
 }
=pod
Threads:  2  Time :   0.5560
Threads:  3  Time :   0.4012
Threads:  4  Time :   0.3664
Threads:  5  Time :   0.2624
Threads:  6  Time :   0.2583
Threads:  7  Time :   0.2549
Threads:  8  Time :   0.2193
Threads:  9  Time :   0.2325
Threads: 10  Time :   0.1514
Threads: 11  Time :   0.1668
Threads: 12  Time :   0.1784
=cut

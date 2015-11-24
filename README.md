# WalkSNC
An efficient SAT solver based on WalkSAT/SKC.

Run makefile to get the executable binary "wsat".

Please use the following format:

./wsat -s seed -n noise*1000 -t maxtime -f maxflips filename

e.g. ./wsat -n 567 to specify the noise to be 0.567.

All the parameters are optional, the default is set to noise=567, maxtime=10, maxflips=1000000, seed=time(0).

Also note that this program is only for exact-3-SAT.

The noise, seed, maxtime, maxflips, solution, running time and total steps are reported.

The solution format is like:

v 1 -2 -3 4 5 6 -7 8 -9 10
v -11 12 13 -14 -15 16 -17 18 -19 -20
v -21 -22 23 24 -25 26 27 -28 -29 -30
...


Each line begin with 'v' contains 10 variables' assignments, and '-' represents false value.

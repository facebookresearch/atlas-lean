# MGreedy Reaches

`MGreedyReaches L T R`: some run of **MGREEDY** started from the working list `L` and the
finished list `T` ends with the finished list `R`. At each step positions `i, j` (possibly equal)
of maximum overlap among all ordered pairs are chosen, ties broken arbitrarily; if `i ≠ j` the
two strings are replaced by their merge, and if `i = j` the string moves to the finished list.

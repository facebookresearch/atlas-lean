# Leftist heap from a list by tail-recursive merging

Over a linear order, the leftist heap built from a list $[x_1, \dots, x_n]$ is obtained by forming
the list of singleton heaps of $x_1, \dots, x_n$ and merging all of them by repeated passes of
tail-recursive adjacent merging (with fuel $n$, which suffices). The empty list gives the empty
heap.

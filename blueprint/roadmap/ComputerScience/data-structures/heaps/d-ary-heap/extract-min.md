# Extracting the minimum of a $d$-ary min-heap

For a $d$-ary min-heap $h$,
extracting the minimum returns nothing if the storage array of $h$ is empty. Otherwise it
returns the root entry (the entry at index $0$) together with the heap obtained from $h$ by
removing its root: the last entry moves to the root and sifts down along a single $d$-ary
child path.

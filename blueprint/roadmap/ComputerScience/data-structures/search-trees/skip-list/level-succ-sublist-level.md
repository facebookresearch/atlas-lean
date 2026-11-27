# Each skip-list level is a subsequence of the level below

For every skip list and every
level index $i$ (levels are numbered from $0$ at the bottom), the list of key-value pairs visible
at level $i + 1$ is a subsequence, not necessarily contiguous, of the list of key-value pairs
visible at level $i$.

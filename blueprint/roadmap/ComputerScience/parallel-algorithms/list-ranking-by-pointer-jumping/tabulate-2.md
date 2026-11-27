# Tabulating a list-ranking state

The tabulation of a pointer-jumping state $s$ on the
nodes $0, \dots, n - 1$ is the pair of arrays of length $n$ whose entries at $v$ are the pointer
and the distance of $v$ in $s$.

Evaluating the state after $t$ rounds directly re-reads earlier rounds' pointers at every query,
a cost growing exponentially with the number of rounds; the tabulated rounds cost $O(n)$ array
operations each.

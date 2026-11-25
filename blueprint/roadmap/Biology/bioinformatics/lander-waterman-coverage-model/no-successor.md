# Read with no successor

For read length $L$ and start positions $s_1, \dots, s_N$ on a circular genome of length $G$, read $j$ has no successor if no other read $j' \ne j$ satisfies $0 < (s_{j'} - s_j) \bmod G < L$: no other read starts in the $L - 1$ positions after $s_j$. Several no-successor reads can lie in one island, so their number is not the island count.

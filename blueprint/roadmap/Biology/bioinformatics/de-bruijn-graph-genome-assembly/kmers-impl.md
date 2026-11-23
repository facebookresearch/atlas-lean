# Efficient executable computation of k-mers

For $k$ and a string $s$ of length $L$, the list obtained by taking the first $\max(L + 1 - k, 0)$ suffixes $s, s_1 s_2 \cdots, \dots$ of $s$ and truncating each to its first $k$ letters. It is the list of [$k$-mers](kmers.md) of $s$, computed in $O(Lk)$ steps.

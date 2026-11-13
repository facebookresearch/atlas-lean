# Pile kept by the M-rule

For a position $x \in \mathbb{N}^{n+1}$ with piles indexed by
$0, \dots, n$: if some entry of $x$ is even, the kept pile is the least index $i$ such that $x_i$
is even and $x_i \le x_j$ for every $j$ with $x_j$ even; otherwise it is the least index $i$
such that $x_j \le x_i$ for every $j$.

## Sources

- Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1, Section 2 (the index `e(x)`). Such a pile always exists, so the default `0` of `getD` is never used.

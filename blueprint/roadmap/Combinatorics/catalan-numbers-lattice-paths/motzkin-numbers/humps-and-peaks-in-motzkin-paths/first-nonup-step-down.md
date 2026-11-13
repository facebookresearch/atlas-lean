# Paths whose first non-up step is down

Write a path of length $n$ as a sequence of steps
$p_0, \dots, p_{n-1}$, each $D$ (down), $F$ (flat) or $U$ (up), encoded as $0$, $1$, $2$. The
path has first non-up step down when there is a position $i$ with $p_i = D$ and $p_j = U$ for
every $j < i$. In particular, a path all of whose steps are up steps, including the empty path,
does not qualify.

For a Motzkin prefix ending at height $h$, this is membership in the paper's set
$\mathcal{M}^{D*}_{n,h}$.

## Sources

- Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).

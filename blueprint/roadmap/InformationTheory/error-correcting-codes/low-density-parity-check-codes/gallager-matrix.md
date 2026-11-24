# Gallager's $(n, j, k)$ matrix with $n = mk$

Let $n = mk$. Gallager's matrix has $jm$ rows, indexed by a block $t < j$ and a row $r < m$, and
$n$ columns. Its entry in row $(t, r)$ and column $c$ is $1$ if $\lfloor \pi_t(c) / k \rfloor = r$
and $0$ otherwise, where $\pi_t$ is the [permutation of block $t$](block-perm.md). So block $0$ has
its ones "in descending order", row $r$ being $1$ on the columns $rk, \dots, rk + k - 1$ (counting
from $0$), and every other block is block $0$ with its columns permuted. Gallager's Figure 2.1 is
the case $n = 20$, $j = 3$, $k = 4$.

Gallager's ensemble of $(n, j, k)$ codes is the law of this matrix when $\sigma_1, \dots, \sigma_{j-1}$
are independent and uniform over all permutations of the columns ("random permutations of the
columns of each of the bottom $j - 1$ submatrices"). The theorems on this topic hold for every choice
of the permutations, hence for every matrix of the ensemble.

## Background

- [Column permutations of Gallager's ensemble](block-perm.md)

## Sources

- R. G. Gallager, *Low-Density Parity-Check Codes*, MIT Press, 1963, Section 2.2 (p. 13 of the author's retypeset PDF, web.mit.edu/gallager/www/pages/ldpc.pdf), and Figure 2.1.

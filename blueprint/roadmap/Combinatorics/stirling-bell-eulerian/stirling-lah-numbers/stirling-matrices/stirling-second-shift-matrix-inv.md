# Inverse of a shifted Stirling matrix

For natural numbers $m$ and $n$, let $S^{[m]}(n)$ be
the $n \times n$ rational matrix with entries $S(i + m, j)$, where $S(i, j)$ denotes the Stirling
numbers of the second kind; let $s(n)$ be the matrix with entries the signed Stirling numbers of
the first kind $s(i, j)$; and let $\tilde V(n)$ be the upper triangular matrix with
$\tilde V(n)_{i,j} = (-1)^{j-i} (i-1)!/j!$ for $j \ge i$ and $\tilde V(n)_{i,j} = 0$ for $j < i$,
all indices running over $1, \dots, n$. Then $S^{[m]}(n)^{-1} = \tilde V(n)^m\, s(n)$.

The paper assumes $m \ge 1$; the case $m = 0$, which reads $S^{[0]}(n)^{-1} = s(n)$, holds as well.

## Sources

- M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*, INTEGERS 25 (2025), Article A27, Theorem 3 (`integers-2025-A27-thm-3`).

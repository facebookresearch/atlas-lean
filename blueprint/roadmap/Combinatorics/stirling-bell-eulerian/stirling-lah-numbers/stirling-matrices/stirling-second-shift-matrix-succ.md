# Recurrence for shifted Stirling matrices

For natural numbers $m$ and $n$, let $S^{[m]}(n)$
be the $n \times n$ rational matrix with entries $S(i + m, j)$, where $S(i, j)$ denotes the
Stirling numbers of the second kind, and let $V(n)$ be the upper bidiagonal matrix with
$V(n)_{i,i} = i$, $V(n)_{i,i+1} = 1$ and all other entries $0$, all indices running over
$1, \dots, n$. Then $S^{[m+1]}(n) = S^{[m]}(n)\, V(n)$ and
$\det S^{[m+1]}(n) = n! \cdot \det S^{[m]}(n)$.

## Sources

- M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*, INTEGERS 25 (2025), Article A27, Corollary 2 (`integers-2025-A27-cor-2`).

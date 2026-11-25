# Double-sum Kronecker delta identity for Stirling numbers

Write $S(n, k)$ for the Stirling
numbers of the second kind and $s(n, k)$ for the signed Stirling numbers of the first kind. For
all natural numbers $i, j, n$ with $i \ge 1$, $n \ge i$ and $n \ge j$, in the rational numbers,

$$\sum_{k_1=1}^{n} \sum_{k_2=k_1}^{n} (-1)^{k_2-k_1} \frac{(k_1-1)!}{k_2!}\,
S(i+1, k_1)\, s(k_2, j) = \delta_{i,j},$$

where $\delta_{i,j}$ is $1$ if $i = j$ and $0$ otherwise.

The hypothesis $i \ge 1$ cannot be dropped: for $i = j = 0$ the left side is $0$. The source's
hypothesis $j \ge 1$ is not needed.

## Sources

- M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*, INTEGERS 25 (2025), Article A27, Theorem 6.

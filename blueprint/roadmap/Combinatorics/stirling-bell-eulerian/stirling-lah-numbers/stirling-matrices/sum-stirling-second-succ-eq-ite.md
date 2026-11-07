# Stirling numbers of the second kind from the next row

Write $S(n, k)$ for the Stirling
numbers of the second kind. For all natural numbers $i \ge 1$ and $j$, the rational number

$$\sum_{k=1}^{\min(i+1, j)} (-1)^{j-k} \frac{(k-1)!}{j!} S(i+1, k)$$

equals $S(i, j)$ if $j \le i$ and $0$ if $j > i$.

The case $j = 0$, where both sides vanish, is included although the source assumes $j \ge 1$.

## Sources

- M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*, INTEGERS 25 (2025), Article A27, Theorem 7 (`integers-2025-A27-thm-7`).

# Closed form for three-dimensional lattice points with bounded $\ell^1$ norm

The following holds. For $k, n \in \mathbb{N}$, let $a_{n,k}^{(3)}$ be the number of integer points $(x_1, x_2, x_3)$ with $\lvert x_i \rvert \le k$ for every $i$ and $\lvert x_1 \rvert + \lvert x_2 \rvert + \lvert x_3 \rvert \le n$. Then

$$3 a_{n,k}^{(3)} = \begin{cases} 4n^3 + 6n^2 + 8n + 3, & n < k, \\ 12k^3 - 36k^2 n + 36k n^2 - 8n^3 + 6n^2 + 6k + 2n + 3, & k \le n < 2k, \\ -84k^3 + 108k^2 n - 36k n^2 + 4n^3 - 72k^2 + 72nk - 12n^2 - 6k + 8n + 3, & 2k \le n < 3k, \\ 24k^3 + 36k^2 + 18k + 3, & n \ge 3k, \end{cases}$$

with the right-hand side computed in $\mathbb{Z}$.

## Sources

- Sela Fried, "Proofs of Several Conjectures From the OEIS", Journal of Integer Sequences 28 (2025), Article 25.4.3, Corollary 2.

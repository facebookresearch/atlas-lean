# Generating function for lattice points with given $\ell^1$ norm

The following holds. For all $m, k \in \mathbb{N}$, let $b_{n,k}^{(m)}$ be the number of integer points $(x_1, \dots, x_m)$ with $\lvert x_i \rvert \le k$ for every $i$ and $\sum_i \lvert x_i \rvert = n$. Then, as formal power series over $\mathbb{Q}$,

$$\sum_{n \ge 0} b_{n,k}^{(m)} x^n = \left(1 + \frac{2x(1 - x^k)}{1 - x}\right)^m,$$

where $\frac{1}{1-x}$ is the inverse of $1 - x$ in $\mathbb{Q}[[x]]$. No positivity is assumed: for $k = 0$ or $m = 0$ both sides equal $1$.

## Sources

- Sela Fried, "Proofs of Several Conjectures From the OEIS", Journal of Integer Sequences 28 (2025), Article 25.4.3, Theorem 1.

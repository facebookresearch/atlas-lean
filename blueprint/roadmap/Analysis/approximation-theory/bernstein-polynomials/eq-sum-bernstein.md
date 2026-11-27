# Expansion of a polynomial in the Bernstein basis

For integers $0 \le \nu \le n$, the Bernstein polynomial is $b_{n,\nu}(s) = \binom{n}{\nu} s^{\nu} (1 - s)^{n - \nu}$, a real polynomial in $s$. Every real polynomial $p$ of degree at most $n$ (the zero polynomial included) satisfies the polynomial identity

$$p = \sum_{j=0}^{n} c_j\, b_{n,j}, \qquad c_j = \sum_{k=0}^{n} p_k \frac{\binom{j}{k}}{\binom{n}{k}},$$

where $p_k$ is the coefficient of $s^k$ in $p$ and $\binom{j}{k} = 0$ for $j < k$.

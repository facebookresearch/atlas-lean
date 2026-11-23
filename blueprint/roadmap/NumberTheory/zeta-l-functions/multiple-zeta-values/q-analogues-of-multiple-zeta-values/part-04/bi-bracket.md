# Bi-brackets

For integers $k_1, \dots, k_r \ge 1$ and $d_1, \dots, d_r \ge 0$, the
bi-bracket is the $q$-series

$$
g(k_1, \dots, k_r; d_1, \dots, d_r) =
\sum_{m_1 > \dots > m_r > 0} \, \sum_{n_1, \dots, n_r > 0} \, \prod_{j=1}^{r}
\frac{m_j^{d_j}}{d_j!} \frac{n_j^{k_j - 1}}{(k_j - 1)!} \, q^{m_1 n_1 + \dots + m_r n_r},
$$

and $g(\varnothing; \varnothing) = 1$. The summands with $m_1 > N$ have $q$-adic order greater
than $N$, so the coefficient of $q^N$ is that of the finite partial sum over $m_1 \le N$; this
is how the series is defined.

The same formula, with $k_j - 1$ read as $0$, defines a value when some $k_j = 0$.

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, Definition-Proposition of bi-brackets (after Bachmann).

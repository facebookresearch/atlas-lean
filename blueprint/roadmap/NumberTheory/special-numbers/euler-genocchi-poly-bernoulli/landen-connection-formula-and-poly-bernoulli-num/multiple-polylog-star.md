# Non-strict multiple polylogarithm

For an index $k = (k_1, \dots, k_r)$ of positive
integers with $r \ge 1$, the non-strict multiple polylogarithm is the formal power series

$$\mathrm{Li}^\star_k(z) = \sum_{0\lt m_1\le\cdots\le m_r} \frac{z^{m_r}}{m_1^{k_1} \cdots m_r^{k_r}}$$

in $\mathbb{R}[[z]]$.

The definition accepts every finite list $k$ of natural numbers: for $r \ge 1$ the coefficient
of $z^m$ is the sum of $1/(m_1^{k_1} \cdots m_r^{k_r})$ over $0 \le m_1 \le \cdots \le m_r = m$,
where $0^0 = 1$ and $1/0 = 0$ (so for an index the terms with some $m_i = 0$ vanish), and the
empty list gives the constant series $1$.

## Sources

- Ken Kamano, *A Generalization of the Landen Connection Formula and Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 1.

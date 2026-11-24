# Schlesinger–Zudilin qMZVs

For an index $k = (k_1, \dots, k_r)$ of natural numbers, the
Schlesinger–Zudilin qMZV $\zeta_q^{SZ}(k)$ is the formal power series in $q$ over $\mathbb{Q}$
whose coefficient of $q^N$, for each $N \ge 0$, is the coefficient of $q^N$ in the partial sum

$$\sum_{N \ge m_1 > \dots > m_r > 0} \prod_{j=1}^{r} \frac{q^{m_j k_j}}{(1 - q^{m_j})^{k_j}}$$

over integers $m_1, \dots, m_r$. In particular $\zeta_q^{SZ}(\emptyset) = 1$.

When the index is empty or $k_1 \ge 1$, the summands with $m_1 > N$ have no term of degree at
most $N$, so $\zeta_q^{SZ}(k)$ is the full series
$\sum_{m_1 > \dots > m_r > 0} \prod_{j} q^{m_j k_j} / (1 - q^{m_j})^{k_j}$. The paper does not
define the value when $k_1 = 0$.

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, Definition of Schlesinger–Zudilin qMZVs (extended version of Ebrahimi-Fard, Manchon and Singer, allowing `kⱼ = 0` for `j ≥ 2`).

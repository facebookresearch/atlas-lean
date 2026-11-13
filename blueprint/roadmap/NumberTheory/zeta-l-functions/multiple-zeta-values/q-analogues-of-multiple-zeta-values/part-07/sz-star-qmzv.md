# SZ-star qMZVs

For an index $k = (k_1, \dots, k_r)$ of natural numbers, the SZ-star qMZV
$\zeta_q^{SZ,\star}(k)$ is the formal power series in $q$ over $\mathbb{Q}$

$$
\zeta_q^{SZ,\star}(k_1, \dots, k_r) =
\sum_{m_1 \ge \dots \ge m_r > 0} \prod_{j=1}^{r} \frac{q^{m_j k_j}}{(1 - q^{m_j})^{k_j}},
$$

with $\zeta_q^{SZ,\star}(\varnothing) = 1$. Precisely, its coefficient of $q^N$ is defined as the
coefficient of $q^N$ in the partial sum over $N \ge m_1 \ge \dots \ge m_r > 0$. For $k_1 \ge 1$ the
summands with $m_1 > N$ have $q$-adic order $> N$, so this is the coefficient of $q^N$ in the full
sum; for $k_1 = 0$ the full sum is not a formal power series and the value is a junk value.

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, Theorem 17 (iii) (the map `ζ_q^{SZ,⋆}` of SZ-star qMZVs).

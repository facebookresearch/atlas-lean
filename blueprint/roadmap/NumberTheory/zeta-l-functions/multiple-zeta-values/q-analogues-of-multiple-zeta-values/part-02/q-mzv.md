# General q-multiple zeta values

For natural numbers $k_1, \dots, k_r$ and polynomials
$Q_1, \dots, Q_r \in \mathbb{Q}[X]$, the general qMZV $\zeta_q(k_1, \dots, k_r; Q_1, \dots, Q_r)$
is the formal power series in $q$ over $\mathbb{Q}$ whose coefficient of $q^N$, for every $N$, is
the coefficient of $q^N$ in the finite sum
$\sum_{N \ge m_1 > m_2 > \dots > m_r > 0} \prod_{j=1}^{r} Q_j(q^{m_j}) / (1 - q^{m_j})^{k_j}$
over integers $m_1, \dots, m_r$, and $\zeta_q(\varnothing; \varnothing) = 1$.

When $Q_1(0) = 0$ (the paper's condition $Q_1 \in X \mathbb{Q}[X]$), the summands with
$m_1 > N$ have $q$-adic order greater than $N$, so this is the series
$\sum_{m_1 > \dots > m_r > 0} \prod_{j=1}^{r} Q_j(q^{m_j}) / (1 - q^{m_j})^{k_j}$; for other data
the value is a junk value.

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, Definition of qMZVs (after Bachmann–Kühn).

# Coefficients of Schlesinger–Zudilin qMZVs as sums of binomial products

Let $r \ge 0$,
and let $k_1, \dots, k_r$ and $d_1, \dots, d_r$ be positive integers. For every natural number
$N$, the coefficient of $q^N$ in the Schlesinger–Zudilin qMZV
$\zeta_q^{\mathrm{SZ}}(k_1, \{0\}^{d_1 - 1}, \dots, k_r, \{0\}^{d_r - 1})$, whose index lists each
$k_j$ followed by $d_j - 1$ zeros, equals

$$\sum \prod_{j=1}^{r} \binom{n_j - 1}{k_j - 1} \binom{m_j - m_{j+1} - 1}{d_j - 1},$$

where the sum runs over all integers $m_1 > \dots > m_r > 0$ and $n_1, \dots, n_r \ge 1$ with
$m_1 n_1 + \dots + m_r n_r = N$, and where $m_{r+1} = 0$.

These are the coefficients of $X_1^{k_1 - 1} \cdots X_r^{k_r - 1} Y_1^{d_1 - 1} \cdots
Y_r^{d_r - 1} q^N$ on both sides of the paper's identity expressing the generating series
$s(X; Y)$ of these qMZVs as
$\sum \prod_j (1 + X_j)^{n_j - 1} (1 + Y_j)^{m_j - m_{j+1} - 1} q^{m_j n_j}$.

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, Theorem 4 (`integers-2024-A6-thm-4`).

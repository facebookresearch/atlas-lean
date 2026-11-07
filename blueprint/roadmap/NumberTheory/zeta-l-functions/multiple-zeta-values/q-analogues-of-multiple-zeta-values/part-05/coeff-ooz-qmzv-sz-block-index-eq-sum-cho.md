# Generating series of OOZ-qMZVs, coefficientwise

Let $r$ and $N$ be natural numbers and
let $k_1, \dots, k_r \ge 1$ and $d_1, \dots, d_r \ge 0$ be integers. Writing $\{0\}^d$ for $d$
consecutive zeros, the coefficient of $q^N$ in the Ohno–Okuda–Zudilin qMZV
$\zeta_q^{\mathrm{OOZ}}(k_1, \{0\}^{d_1}, \dots, k_r, \{0\}^{d_r})$ equals the coefficient of
$q^N$ in

$$\sum q^{m_1} \prod_{j=1}^r \binom{m_j - m_{j+1} - 1}{d_j} \frac{1}{(1 - q^{m_j})^{k_j}},$$

the sum running over integers $N \ge m_1 > m_2 > \dots > m_r > 0$, where $m_{r+1} := 0$ and the
factor $q^{m_1}$ is read as $1$ when $r = 0$.

In the untruncated sum, the summands with $m_1 > N$ have $q$-adic order greater than $N$. Let
$\mathfrak{oz}(X; Y)$ be the paper's generating series of OOZ-qMZVs of depth $r$ in the variables
$X_1, \dots, X_r$ and $Y_1, \dots, Y_r$ over $\mathbb{Q}[[q]]$. The statement compares the
coefficients of $\prod_j X_j^{k_j}/k_j! \, Y_j^{d_j}$ on both sides of the paper's identity
$\mathfrak{oz}(X; Y) = \sum q^{m_1} \prod_j (1 + Y_j)^{m_j - m_{j+1} - 1}
(e^{X_j/(1 - q^{m_j})} - 1)$.

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, Proposition 11 (`integers-2024-A6-prop-11`).

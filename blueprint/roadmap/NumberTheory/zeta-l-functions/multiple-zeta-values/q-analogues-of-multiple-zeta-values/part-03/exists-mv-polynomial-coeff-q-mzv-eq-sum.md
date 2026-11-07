# Coefficients of qMZVs as polynomial functions on partitions

Let $r \ge 1$ and let
$(k_1, Q_1), \dots, (k_r, Q_r)$ be pairs of a natural number $k_j$ and a polynomial
$Q_j \in \mathbb{Q}[X]$ with $\deg Q_j \le k_j$ for every $j$ and $Q_1(0) = 0$. For $s, N \ge 0$
let $\mathcal{P}_s(N)$ be the set of pairs $(\mathbf{m}, \mathbf{n})$ of tuples
$\mathbf{m} = (m_1, \dots, m_s)$ and $\mathbf{n} = (n_1, \dots, n_s)$ of positive integers with
$m_1 > \cdots > m_s$ and $m_1 n_1 + \cdots + m_s n_s = N$ (the partitions of $N$ with $s$
distinct parts $m_i$, of multiplicities $n_i$). Then there are polynomials
$f_s \in \mathbb{Q}[X_1, \dots, X_s, Y_1, \dots, Y_s]$, one for each $s \ge 0$, such that for
every $N \ge 0$ the coefficient of $q^N$ in the general qMZV
$\zeta_q(k_1, \dots, k_r; Q_1, \dots, Q_r)$ equals

$$\sum_{s=1}^{r} \sum_{(\mathbf{m}, \mathbf{n}) \in \mathcal{P}_s(N)} f_s(\mathbf{m}, \mathbf{n}),$$

where $f_s(\mathbf{m}, \mathbf{n})$ is the value of $f_s$ at $X_i = m_i$, $Y_i = n_i$.

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, Theorem 18 (`integers-2024-A6-thm-18`).

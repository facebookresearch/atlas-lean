# Partial sums of bi-brackets

For pairs $(k_1, d_1), \dots, (k_r, d_r)$ of natural numbers
and a bound $M \in \mathbb{N}$, the partial bi-bracket is the $q$-series

$$
\sum_{M > m_1 > \dots > m_r > 0} \, \prod_{j=1}^{r} \frac{m_j^{d_j}}{d_j!} E_{k_j}(m_j),
$$

where $E_k(m) = \sum_{n \ge 1} \frac{n^{k-1}}{(k-1)!} q^{mn}$ is the Eulerian $q$-series (with
$k - 1$ read as $0$ when $k = 0$). For $r = 0$ it is $1$.

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, Definition-Proposition of bi-brackets (defining sum truncated at `m₁ < M`).

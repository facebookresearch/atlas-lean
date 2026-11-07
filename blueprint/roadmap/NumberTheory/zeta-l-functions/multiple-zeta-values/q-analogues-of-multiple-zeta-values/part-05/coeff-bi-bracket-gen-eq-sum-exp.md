# Bi-bracket generating series as a sum of exponentials

Let $r$ and $N$ be natural numbers
and let $g(X_1, \dots, X_r; Y_1, \dots, Y_r)$ be the generating series of bi-brackets of depth $r$,
a power series in the $2r$ variables over $\mathbb{Q}[[q]]$. The power series over $\mathbb{Q}$
obtained by taking the coefficient of $q^N$ in every coefficient of $g$ equals the finite sum

$$\sum \prod_{j=1}^r e^{m_j Y_j} e^{n_j X_j}$$

over all integers $m_1 > m_2 > \dots > m_r > 0$ and $n_1, \dots, n_r \ge 1$ with
$m_1 n_1 + \dots + m_r n_r = N$, where $e^Z$ is the exponential series evaluated at $Z$.

This is the $q^N$-part of the identity
$g(X; Y) = \sum \prod_j e^{m_j Y_j} e^{n_j X_j} q^{m_j n_j}$.

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, Theorem 11 (after Bachmann) (`integers-2024-A6-thm-11`).

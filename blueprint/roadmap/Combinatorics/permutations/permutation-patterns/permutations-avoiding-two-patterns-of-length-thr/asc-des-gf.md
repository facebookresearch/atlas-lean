# Ascent–descent generating function of a pair of patterns

For permutations $\tau$ and
$\rho$ of $\{0, 1, 2\}$, let $S_n(\tau, \rho)$ be the set of permutations of
$\{0, 1, \dots, n-1\}$ that contain neither $\tau$ nor $\rho$ as a classical pattern. The
ascent–descent generating function of $(\tau, \rho)$ is the formal power series

$$\sum_{n \ge 0} \sum_{\sigma \in S_n(\tau, \rho)}
x^n p^{\mathrm{asc}(\sigma)} q^{\mathrm{des}(\sigma)}$$

in $x$ with coefficients in the polynomial ring $\mathbb{Q}[p, q]$, where $\mathrm{asc}(\sigma)$
and $\mathrm{des}(\sigma)$ are the numbers of ascents and descents of $\sigma$. The empty
permutation ($n = 0$) contributes the constant term $1$.

## Sources

- Han, *Joint Distributions of 10 Classical Statistics over Permutations Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`asc`, `des`).

# Goemans-Williamson rounding for MAX-2SAT

Let $v_0, \dots, v_n$ be unit vectors that are $\varepsilon$-optimal for the MAX-2SAT relaxation of a weighted 2-CNF formula $\varphi$. Draw a standard Gaussian vector $g$ and set $x_i$ true iff $\mathrm{sign}\langle g, v_i \rangle = \mathrm{sign}\langle g, v_0\rangle$. Then the expected satisfied weight is at least $\alpha_{GW}(Z_{\mathrm{SDP}} - \varepsilon) \ge \alpha_{GW} \cdot \mathrm{OPT}(\varphi) - \alpha_{GW}\varepsilon$, where $\alpha_{GW} = \min_{0 < \theta \le \pi} \frac{2}{\pi}\frac{\theta}{1 - \cos\theta} > 0.87856$. The bound applies verbatim to counts of satisfied clauses of an unweighted 2-CNF instance.

## Proof sketch

By linearity it suffices to compare each term: the random hyperplane separates $v_i, v_j$ with probability $\theta_{ij}/\pi$, and $\theta/\pi \ge \alpha_{GW}\frac{1 - \cos\theta}{2}$, $1 - \theta/\pi \ge \alpha_{GW}\frac{1 + \cos\theta}{2}$.

## Depends on

- [The semidefinite relaxation of MAX-2SAT](max-two-sat-semidefinite-relaxation.md)

## Proof depends on

- [Goemans–Williamson Lemma 3.2: probability that a random hyperplane separates two unit vectors](../goemans-williamson-max-cut-algorithm/measure-real-sign-ne.md)
- [The Goemans–Williamson constant is a lower bound for the ratio](../goemans-williamson-max-cut-algorithm/gw-constant-le.md)

## Sources

- M. X. Goemans and D. P. Williamson, "Improved Approximation Algorithms for Maximum Cut and Satisfiability Problems Using Semidefinite Programming", Journal of the ACM 42(6), 1995.

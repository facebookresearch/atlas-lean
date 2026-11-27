# Variance decomposition of a mixed Poisson law

Let $\nu$ be a probability measure on $\mathbb{R}$ concentrated on $[0, \infty)$ with
$\int r^2\, d\nu < \infty$, and let $p_\nu$ be the [mixed Poisson mass function](poisson-mixture-real.md).
Then

$$\sum_{k \ge 0} k^2 p_\nu(k) - \Bigl(\sum_{k \ge 0} k\, p_\nu(k)\Bigr)^2 = \mathbb E \Lambda + \operatorname{Var} \Lambda,$$

with $\Lambda \sim \nu$: Poisson noise plus the variance of the rate.

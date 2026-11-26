# Squared coefficient of variation of a mixed Poisson law

Let $\nu$ be a probability measure on $\mathbb{R}$ concentrated on $[0, \infty)$, with
$\int r^2\, d\nu < \infty$ and $\mathbb E \Lambda = \int r\, d\nu > 0$, and let $p_\nu$ be the [mixed
Poisson mass function](poisson-mixture-real.md). Then, for $N \sim p_\nu$,

$$\mathrm{CV}^2(N) = \frac{\sum_k k^2 p_\nu(k) - \bigl(\sum_k k\, p_\nu(k)\bigr)^2}{\bigl(\sum_k k\, p_\nu(k)\bigr)^2} = \frac{1}{\mathbb E \Lambda} + \frac{\operatorname{Var} \Lambda}{(\mathbb E \Lambda)^2},$$

that is $\mathrm{CV}^2(N) = 1/\mathbb E \Lambda + \mathrm{CV}^2(\Lambda)$, where $\Lambda \sim \nu$.

## Sources

- P. Brennecke et al., *Accounting for technical noise in single-cell RNA-seq experiments*, Nature Methods 10 (2013), 1093–1095.
- V. Svensson, *Droplet scRNA-seq is not zero-inflated*, Nature Biotechnology 38 (2020), 147–150.

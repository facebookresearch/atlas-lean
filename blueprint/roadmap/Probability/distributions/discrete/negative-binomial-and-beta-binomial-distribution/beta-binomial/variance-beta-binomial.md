# Variance of the beta-binomial law

For $n \in \mathbb{N}$ and $\alpha, \beta > 0$, with $\pi = \alpha/(\alpha + \beta)$ and
$\gamma = 1/(\alpha + \beta + 1)$,

$$\sum_{k=0}^{n} k^2\, \mathrm{BB}(n; \alpha, \beta)(k) - \Bigl( \sum_{k=0}^{n} k\, \mathrm{BB}(n; \alpha, \beta)(k) \Bigr)^2 = n \pi (1 - \pi) \bigl(1 + (n - 1)\gamma\bigr),$$

where $\mathrm{BB}$ is the [beta-binomial mass function](beta-binomial-pmf.md); this is the
Dolzhenko–Smith parametrization of the variance.

## Sources

- E. Dolzhenko and A. D. Smith, *Using beta-binomial regression for high-precision differential methylation analysis in multifactor whole-genome bisulfite sequencing experiments*, BMC Bioinformatics 15 (2014), 215.

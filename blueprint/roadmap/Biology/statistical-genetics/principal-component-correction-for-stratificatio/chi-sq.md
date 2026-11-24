# EIGENSTRAT association statistic

Let $V \subseteq \mathbb{R}^N$ be a linear subspace, let $K$ be a natural number and let $y, g \in \mathbb{R}^N$ (a phenotype and a genotype). The EIGENSTRAT statistic is (Price et al. 2006)

$$\chi^2 = (N - K - 1)\, \frac{\langle r_V(g), r_V(y) \rangle^2}{\|r_V(g)\|^2\, \|r_V(y)\|^2},$$

where $r_V$ is the [residual](adjusted.md), $N - K - 1$ is computed in the reals, and $x/0 = 0$ (so $\chi^2 = 0$ when either residual vanishes). The fraction is the squared cosine of the residuals, which equals their squared sample correlation when both are centred.

## Sources

- A. L. Price, N. J. Patterson, R. M. Plenge, M. E. Weinblatt, N. A. Shadick and D. Reich, *Principal components analysis corrects for stratification in genome-wide association studies*, Nat. Genet. 38 (2006), 904–909.

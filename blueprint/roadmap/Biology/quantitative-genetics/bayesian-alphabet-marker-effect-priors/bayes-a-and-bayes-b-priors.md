# BayesA and BayesB marker-effect priors

Write $\chi^{-2}(\nu, s^2)$ for the scaled inverse chi-square law, the law of $\nu s^2/W$ with $W \sim \chi^2_\nu$; its density on $(0, \infty)$ is proportional to $(\sigma^2)^{-(\nu/2+1)}\exp\!\big(-\nu s^2/(2\sigma^2)\big)$.

Consider the genomic regression $y_i = \mu + \sum_{j=1}^{m} x_{ij}^\top g_j + e_i$, $e_i \sim N(0, \sigma_e^2)$ independent, where $g_j \in \mathbb{R}^{d_j}$ collects the effects of chromosome segment (or marker) $j$ and $x_{ij}$ the corresponding genotype codes of individual $i$.

**BayesA.** Independently over $j$,

$$g_j \mid \sigma_j^2 \sim N(0, \sigma_j^2 I_{d_j}), \qquad \sigma_j^2 \sim \chi^{-2}(\nu, s^2).$$

Each segment has its own effect variance. For a single effect ($d_j = 1$) the marginal prior of $g_j$ is the scaled Student law $s\,t_\nu$, which has heavier tails than the normal prior of ridge regression (BLUP), so small effects are shrunk strongly and large effects weakly. Conditional conjugacy gives the Gibbs update

$$\sigma_j^2 \mid g_j \sim \chi^{-2}\!\left(\nu + d_j,\ \frac{\nu s^2 + g_j^\top g_j}{\nu + d_j}\right).$$

**BayesB.** The prior of $\sigma_j^2$ is the mixture

$$\sigma_j^2 = 0 \ \text{with probability } \pi, \qquad \sigma_j^2 \sim \chi^{-2}(\nu, s^2) \ \text{with probability } 1 - \pi,$$

so a fraction $\pi$ of segments has no effect at all. Since $\sigma_j^2 = 0$ forces $g_j = 0$ and conversely, a Gibbs sampler that alternates $g_j \mid \sigma_j^2$ and $\sigma_j^2 \mid g_j$ cannot leave the point mass; $\sigma_j^2$ is therefore updated by a Metropolis–Hastings step from its conditional distribution given the data with $g_j$ integrated out, followed by sampling $g_j$ given $\sigma_j^2$.

## Depends on

- [Marginal law of the mixed-model response](../linear-mixed-models-and-blup/map-mixed-model-response.md)

## Expansion

If $\sigma_j^2 = \nu s^2/W$ with $W \sim \chi^2_\nu$ and $g_j = \sigma_j Z$ with $Z \sim N(0,1)$ independent, then $g_j = s\,Z/\sqrt{W/\nu}$, a scaled $t_\nu$ variable. Multiplying the prior density of $\sigma_j^2$ by the normal likelihood $(\sigma_j^2)^{-d_j/2}\exp(-g_j^\top g_j/(2\sigma_j^2))$ gives a kernel of the same scaled inverse chi-square form with $\nu + d_j$ degrees of freedom and $\nu s^2 + g_j^\top g_j$ in place of $\nu s^2$. Fixing $\sigma_j^2 = \sigma_g^2/m$ for every $j$ recovers ridge regression (BLUP) on markers.

## Sources

- T. H. E. Meuwissen, B. J. Hayes and M. E. Goddard, "Prediction of total genetic value using genome-wide dense marker maps", Genetics 157 (2001), 1819–1829, <https://doi.org/10.1093/genetics/157.4.1819> (PMC1461589).

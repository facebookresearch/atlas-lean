# Raw second moments of phenotypes in the LD-score model

Take an [LD-score model](../ld-score-regression/model.md) with heritability $h^2$ on a measure
space $(\Omega, \mu)$: square-integrable effects $\beta_1, \dots, \beta_M$ and noise terms
$\varepsilon_i$ with $\int \beta_k \beta_l \, d\mu = (h^2/M)\, \delta_{kl}$,
$\int \varepsilon_i \varepsilon_{i'} \, d\mu = (1 - h^2)\, \delta_{ii'}$ and
$\int \beta_k \varepsilon_i \, d\mu = 0$, where $\delta$ is $1$ on equal indices and $0$
otherwise. Then for every real $N \times M$ genotype matrix $X$, the
[phenotypes](../ld-score-regression/pheno.md) $y = X\beta + \varepsilon$ satisfy, for all
individuals $i$ and $j$,

$$\int y_i\, y_j \, d\mu = h^2 A_{ij} + (1 - h^2)\, \delta_{ij},$$

where $A = XX^\top/M$ is the [genetic relationship matrix](grm.md) ($A = 0$ when $M = 0$). The
measure is arbitrary, so these are raw second moments. When $\mu$ is a probability measure and
the effects and noise have mean zero, the phenotypes have mean zero and
$h^2 A + (1 - h^2) I$ is their covariance matrix.

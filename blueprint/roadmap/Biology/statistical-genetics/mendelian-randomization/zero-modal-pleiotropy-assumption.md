# Zero modal pleiotropy assumption

For genetic variants $G_j$ $(j = 1, \dots, L)$, an exposure $X$ and an outcome $Y$, assume the linear models

$$X \mid G_j = \beta_{X0} + \beta_{Xj}G_j + \lambda_X, \qquad Y \mid G_j = \beta_{Y0} + (\beta\beta_{Xj} + \alpha_j)G_j + \lambda_Y,$$

with $\beta_{Xj} \ne 0$, causal effect $\beta$ and horizontal pleiotropic effect $\alpha_j$. The ratio estimand of variant $j$ is

$$\beta_{Rj} = \frac{\beta_{Yj}}{\beta_{Xj}} = \beta + b_j, \qquad b_j = \frac{\alpha_j}{\beta_{Xj}},$$

so $G_j$ is a valid instrument exactly when $b_j = 0$. Group the variants by the distinct values of $b_j$: $n_0$ variants with $b_j = 0$ and $n_1, \dots, n_k$ variants sharing each distinct nonzero value. The **ZEro Modal Pleiotropy Assumption** (ZEMPA) is

$$n_0 > \max(n_1, \dots, n_k),$$

that is, the most frequent value of $b_j$ is $0$. For weights $w_j$ attached to the variants, the weighted version requires the total weight of the valid variants to exceed the total weight of every group of variants sharing a nonzero bias.

Under ZEMPA the mode of the ratio estimands $\{\beta_{Rj}\}$ is the causal effect $\beta$, even when most variants are invalid.

## Depends on

- [Ratio estimate of a single SNP](ratio-estimate.md)

## Expansion

The mode of the multiset $\{\beta + b_j\}$ is $\beta + b^\dagger$ where $b^\dagger$ is the most frequent bias; ZEMPA says $b^\dagger = 0$. ZEMPA is weaker than the majority-valid condition behind the median estimators: if $n_0 > L/2$, every other group has $n_l \le L - n_0 < n_0$ (and likewise for total weights), so the majority condition implies ZEMPA, but not conversely. With eight variants, two valid and six invalid with distinct biases satisfy ZEMPA but not the majority condition, and ZEMPA fails when three of those six share a bias (Figure 1 of the source).

## Sources

- F. P. Hartwig, G. Davey Smith, J. Bowden, "Robust inference in summary data Mendelian randomization via the zero modal pleiotropy assumption", International Journal of Epidemiology 46 (2017), 1985–1998, <https://doi.org/10.1093/ije/dyx102> (PMC5837715). Methods, Equations (1)–(7).

# Mode-based estimate of a causal effect

Given ratio estimates $\hat\beta_{Rj}$ $(j = 1, \dots, L)$ of the [ratio estimands](zero-modal-pleiotropy-assumption.md) with standard errors $\sigma_{Rj}$, define standardized weights

$$w_j = \frac{\sigma_{Rj}^{-2}}{\sum_{l=1}^L \sigma_{Rl}^{-2}} \quad \text{(weighted MBE)}, \qquad w_j = \frac1L \quad \text{(simple MBE)},$$

and the normal kernel density estimate with bandwidth $h > 0$

$$f(x) = \frac{1}{h\sqrt{2\pi}}\sum_{j=1}^L w_j \exp\!\left[-\frac12\left(\frac{x - \hat\beta_{Rj}}{h}\right)^2\right].$$

The **mode-based estimate** (MBE) is the maximizer $\hat\beta_M = \arg\max_x f(x)$. The bandwidth is $h = \phi s$ with a tuning constant $\phi > 0$ and the modified Silverman rule

$$s = 0.9\, \min\!\big(\operatorname{sd}(\hat\beta_R),\, 1.4826\, \operatorname{mad}(\hat\beta_R)\big)\, L^{-1/5},$$

where $\operatorname{mad}$ is the median absolute deviation from the median. Decreasing $\phi$ trades precision for lower bias. The MBE is consistent for $\beta$ when the (weighted) zero modal pleiotropy assumption holds.

## Depends on

- [Zero modal pleiotropy assumption](zero-modal-pleiotropy-assumption.md)
- [Inverse-variance weight of a ratio estimate](ivw-weight.md)

## Expansion

As the sample size grows each $\hat\beta_{Rj}$ concentrates at $\beta + b_j$, and as the bandwidth shrinks the kernel density concentrates its mass at the distinct values $\beta + b$, each with mass equal to the total weight of the variants with bias $b$. Under ZEMPA the largest mass sits at $\beta$, so the maximizer converges there. Standard errors are obtained by parametric bootstrap.

## Sources

- F. P. Hartwig, G. Davey Smith, J. Bowden, "Robust inference in summary data Mendelian randomization via the zero modal pleiotropy assumption", International Journal of Epidemiology 46 (2017), 1985–1998, <https://doi.org/10.1093/ije/dyx102> (PMC5837715). Methods, Equations (1)–(7).

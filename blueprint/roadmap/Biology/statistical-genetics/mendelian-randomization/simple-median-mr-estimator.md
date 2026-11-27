# Simple median Mendelian randomization estimator

Let $\hat\beta_1, \dots, \hat\beta_J$ be the single-SNP [ratio estimates](ratio-estimate.md)
for $J \ge 1$ genetic variants, and let $\hat\beta_{(1)} \le \hat\beta_{(2)} \le \dots \le \hat\beta_{(J)}$
denote their order statistics. The **simple median Mendelian randomization estimator** is

$$\hat\beta_{\mathrm{M}} = \begin{cases} \hat\beta_{(k+1)} & \text{if } J = 2k + 1, \\ \tfrac{1}{2}\bigl(\hat\beta_{(k)} + \hat\beta_{(k+1)}\bigr) & \text{if } J = 2k. \end{cases}$$

$\hat\beta_{\mathrm{M}}$ has a $50\%$ breakdown point: as sample size $N \to \infty$, with $J$ fixed, if
strictly more than $J/2$ genetic variants are valid instrumental variables (so their ratio estimates
converge in probability to the true causal effect $\beta$), then $\hat\beta_{\mathrm{M}} \xrightarrow{p} \beta$
whatever the estimates of the remaining, invalid variants do.

## Depends on

- [Ratio estimate of a single SNP](ratio-estimate.md)

## Sources

- J. Bowden, G. Davey Smith, P. C. Haycock, and S. Burgess, "Consistent Estimation in Mendelian Randomization with Some Invalid Instruments Using a Weighted Median Estimator", Genetic Epidemiology 40 (2016), 304–314, <https://doi.org/10.1002/gepi.21965> (PMC4849733).

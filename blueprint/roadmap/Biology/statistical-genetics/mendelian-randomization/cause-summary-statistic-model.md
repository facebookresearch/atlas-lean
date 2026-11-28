# CAUSE model of correlated and uncorrelated pleiotropy

Let $M$ (exposure) and $Y$ (outcome) be two traits with GWAS summary statistics $(\hat\beta_{M,j}, \hat s_{M,j})$ and $(\hat\beta_{Y,j}, \hat s_{Y,j})$ at variants $j = 1, \dots, p$, and true marginal associations $\beta_{M,j}, \beta_{Y,j}$. The CAUSE model assumes:

1. **Measurement model.** With a sample-overlap correlation $\rho \in (-1, 1)$,

$$\begin{pmatrix}\hat\beta_{M,j}\\ \hat\beta_{Y,j}\end{pmatrix} \Bigm| \beta_{M,j}, \beta_{Y,j} \sim \mathcal N_2\!\left(\begin{pmatrix}\beta_{M,j}\\ \beta_{Y,j}\end{pmatrix}, S_j(\rho)\right), \qquad S_j(\rho) = \begin{pmatrix} \hat s_{M,j}^2 & \rho\, \hat s_{M,j}\hat s_{Y,j} \\ \rho\, \hat s_{M,j}\hat s_{Y,j} & \hat s_{Y,j}^2 \end{pmatrix}.$$

2. **Structural model.** With independent indicators $Z_j \sim \mathrm{Bernoulli}(q)$ marking variants that act on $M$ through a heritable shared factor $U$ (scaled to have unit effect on $M$),

$$\beta_{Y,j} = \gamma\, \beta_{M,j} + Z_j\, \eta\, \beta_{M,j} + \theta_j,$$

where $\gamma$ is the causal effect of $M$ on $Y$, $\eta$ is the effect of $U$ on $Y$ (correlated pleiotropy) and $\theta_j$ is an uncorrelated pleiotropic effect.

Integrating out $Z_j$ gives the two-component likelihood

$$p\big(\hat\beta_{M,j}, \hat\beta_{Y,j} \mid \beta_{M,j}, \theta_j, \gamma, \eta, q\big) = q\, \mathcal N_2\!\left(\begin{pmatrix}\beta_{M,j}\\ (\gamma+\eta)\beta_{M,j} + \theta_j\end{pmatrix}, S_j(\rho)\right) + (1 - q)\, \mathcal N_2\!\left(\begin{pmatrix}\beta_{M,j}\\ \gamma\beta_{M,j} + \theta_j\end{pmatrix}, S_j(\rho)\right),$$

each normal density evaluated at $(\hat\beta_{M,j}, \hat\beta_{Y,j})$. If $q = 0$ and $\theta_j \equiv 0$ the model reduces to $\beta_{Y,j} = \gamma\beta_{M,j}$, the proportionality assumed by inverse-variance-weighted MR. Causality is tested by comparing the *sharing* model ($\gamma = 0$, $\eta$ and $q$ free) with the *causal* model ($\gamma$ free).

## Depends on

- [Inverse-variance-weighted estimator](ivw.md)
- [Ratio estimate of a single SNP](ratio-estimate.md)

## Expansion

Under the sharing model, the effects $\beta_{Y,j}$ and $\beta_{M,j}$ are correlated only on the fraction $q$ of variants with $Z_j = 1$; under a causal effect every $M$-associated variant shows the correlation. This is the pattern CAUSE uses to separate a shared factor from causation. The two models are compared by the expected log pointwise posterior density, with a one-sided test that the sharing model fits at least as well.

## Sources

- J. Morrison, N. Knoblauch, J. H. Marcus, M. Stephens, X. He, "Mendelian randomization accounting for correlated and uncorrelated pleiotropic effects using genome-wide summary statistics", Nature Genetics 52 (2020), 740–747, <https://doi.org/10.1038/s41588-020-0631-4> (PMC7343608). Methods, Section 4.1, Equations (2)–(7).

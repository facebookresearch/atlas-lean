# Quantile-integrated variance effect of a variant

Let $Y$ be a quantitative phenotype and $G$ a genotype dosage. For $\tau \in (0,1)$ let $Q_Y(\tau \mid G = g) = \alpha_\tau + g\,\beta_\tau$ be the linear quantile-regression model for the conditional $\tau$-quantile of $Y$ given $G$ (phenotype and covariates centred). Define the **quantile-integrated effect**

$$\beta_{QI} = \int_0^{1/2} \big(\beta_{1-\tau} - \beta_\tau\big)\, d\tau .$$

Then:

1. If the genotype shifts the distribution of $Y$ by a location change only, $\beta_\tau \equiv \beta$ is constant in $\tau$ and $\beta_{QI} = 0$: a pure mean effect contributes nothing.
2. If the genotype scales the distribution, $Y = \mu + (1 + g\,\kappa)\,\varepsilon$ with $\varepsilon$ having quantile function $F^{-1}$, then $Q_Y(\tau \mid g) = \mu + F^{-1}(\tau) + g\,\kappa F^{-1}(\tau)$ whenever $1 + g\kappa > 0$, so $\alpha_\tau = \mu + F^{-1}(\tau)$ and $\beta_\tau = \kappa F^{-1}(\tau)$ and $\beta_{QI} = \kappa \int_0^{1/2}(F^{-1}(1-\tau) - F^{-1}(\tau))\,d\tau > 0$ whenever $\kappa > 0$ and $F^{-1}$ is strictly increasing: a variance effect gives a positive, strictly monotone signal in $\kappa$.
3. $\beta_{QI}$ is equivariant under scaling of $Y$ and invariant under adding a constant, so it measures spread rather than level.

A variant with $\beta_{QI} \ne 0$ is a variance quantitative trait locus (vQTL). An alternative, the deviation regression model, regresses $Z_i = |Y_i - \tilde Y_{k(i)}|$ on genotype, where $\tilde Y_k$ is the median of $Y$ in genotype group $k$.

## Depends on

- [Quantile function of a real measure](../../../../Probability/distributions/distribution-functions/quantile-function-and-inverse-transform-sampling/quantile-function/cdf-quantile.md): the conditional quantiles $Q_Y(\tau \mid G)$ and $F^{-1}$

## Proof depends on

- [Monotonicity of the quantile function](../../../../Probability/distributions/distribution-functions/quantile-function-and-inverse-transform-sampling/quantile-function/cdf-quantile-mono-on.md): $F^{-1}(1-\tau) \ge F^{-1}(\tau)$ for $\tau < 1/2$ in item 2

## Expansion

$\beta_{1-\tau} - \beta_\tau$ is the genotype effect on the width of the central $(1-2\tau)$ interquantile range, so integrating it over $\tau \in (0, 1/2)$ aggregates spread effects across the whole distribution while cancelling location effects; the integral is a weighted Gini-type measure of dispersion change. Item 1 follows because the integrand vanishes identically; item 2 from $Q_Y(\tau \mid g) = \mu + (1 + g\kappa)F^{-1}(\tau)$, whose derivative in $g$ is $\kappa F^{-1}(\tau)$, and $F^{-1}(1-\tau) > F^{-1}(\tau)$ for $\tau < 1/2$. Variance effects are of interest because an unmodelled interaction $G \times E$ with an unobserved exposure $E$ induces genotype-dependent residual variance, so vQTL scans can find interacting variants without measuring the exposure. Westerman et al. use the quantile-integrated estimator (QUAIL) for the genome-wide variance scan in a UK Biobank analysis of adiposity-by-genotype effects on cardiometabolic risk factors.

## Sources

- K. E. Westerman, J. E. Gervis, L. J. O'Connor, M. S. Udler, A. K. Manning, "Polygenic scores capture genetic modification of the adiposity-cardiometabolic risk factor relationship", Cell Genomics (2026), <https://doi.org/10.1016/j.xgen.2025.101075> (PMC12985365), STAR Methods, "Genome-wide scans", subsection "Variance effects: genome-wide variance study (vGWAS)".
- J. Miao et al., "A quantile integral linear model to quantify genetic effects on phenotypic variability", Proceedings of the National Academy of Sciences 119 (2022), e2212959119, <https://doi.org/10.1073/pnas.2212959119>.

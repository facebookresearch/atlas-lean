# Correlation of count-split negative binomial counts

Let $X$ follow a [negative binomial distribution](../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/negative-binomial/neg-binomial-real.md) with size $b>0$ and mean $\Lambda>0$, so with variance $\Lambda+\Lambda^2/b$ and overdispersion parameter $b$ (a Poisson–Gamma mixture), and for $\epsilon\in(0,1)$ let $X^{\mathrm{train}}\mid X\sim\operatorname{Binomial}(X,\epsilon)$ and $X^{\mathrm{test}}=X-X^{\mathrm{train}}$ be its [count split](poisson-count-splitting-independence.md). Then $X^{\mathrm{train}}$ and $X^{\mathrm{test}}$ are negative binomial with means $\epsilon\Lambda$ and $(1-\epsilon)\Lambda$ and the same $b$, and

$$\operatorname{Cov}\big(X^{\mathrm{train}},X^{\mathrm{test}}\big)=\frac{\epsilon(1-\epsilon)\Lambda^2}{b},\qquad \operatorname{Corr}\big(X^{\mathrm{train}},X^{\mathrm{test}}\big)=\frac{\sqrt{\epsilon(1-\epsilon)}\,\Lambda}{\sqrt{(\epsilon\Lambda+b)\,\big((1-\epsilon)\Lambda+b\big)}}.$$

The correlation tends to $0$ as $b\to\infty$ (the Poisson limit) and increases as $b$ decreases. The identity quantifies only this correlation. That the null p-values of count splitting stay close to uniform under mild overdispersion and become anti-conservative, approaching those of double dipping, as $b$ decreases is an empirical finding of the source's simulations (with a negative binomial GLM in the testing step), not a consequence of the identity.

## Depends on

- [Poisson count splitting gives independent training and test counts](poisson-count-splitting-independence.md)
- [Negative binomial mass function with size and mean](../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/negative-binomial/neg-binomial-real.md)

## Proof depends on

- [The marginal law of the hierarchy is negative binomial](../../../Probability/bayesian-statistics/gamma-poisson-counts-and-empirical-bayes-shrinka/marginal-lik-eq-neg-binomial-real.md)
- [Variance of the negative binomial law](../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/negative-binomial/variance-neg-binomial.md)

## Expansion

Write $X^{\mathrm{test}}=X-X^{\mathrm{train}}$. By the law of total covariance, $\operatorname{Cov}(X^{\mathrm{train}},X)=\epsilon\operatorname{Var}X$ and $\operatorname{Var}X^{\mathrm{train}}=\epsilon(1-\epsilon)\Lambda+\epsilon^2\operatorname{Var}X$, so $\operatorname{Cov}(X^{\mathrm{train}},X^{\mathrm{test}})=\epsilon(1-\epsilon)(\operatorname{Var}X-\Lambda)$: the covariance is exactly the excess over Poisson variance, scaled by $\epsilon(1-\epsilon)$. Substituting $\operatorname{Var}X=\Lambda+\Lambda^2/b$, $\operatorname{Var}X^{\mathrm{train}}=\epsilon\Lambda+\epsilon^2\Lambda^2/b$ and the analogous test variance gives the correlation. Conditionally on the Gamma-distributed rate the two parts are independent Poisson variables with rates $\epsilon$ and $1-\epsilon$ times that rate, by Poisson count splitting, so each part is again a Gamma–Poisson mixture, hence negative binomial with size $b$; the shared random rate is what correlates them.

## Sources

- A. Neufeld, L. L. Gao, J. Popp et al., "Inference after latent variable estimation for single-cell RNA sequencing data", Biostatistics (2022) kxac047, Section 4.2, Equation (4.14), Proposition 2 (Equation (4.15)) and Figure 2(b), <https://doi.org/10.1093/biostatistics/kxac047>, PMCID PMC12235260.

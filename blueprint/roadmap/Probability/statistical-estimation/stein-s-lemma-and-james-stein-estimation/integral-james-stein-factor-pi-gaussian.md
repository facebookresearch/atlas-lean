# The James–Stein shrinkage factor estimates $1/V$ without bias

If $z \sim \mathcal N_p(0, V I)$ with $V > 0$ and $p \ge 3$, then

$$\mathbb E\, \frac{p - 2}{\|z\|^2} = \frac{1}{V} .$$

In the normal–normal model $\mu_i \sim \mathcal N(0, A)$, $z_i \mid \mu_i \sim \mathcal N(\mu_i, 1)$, independently for $i = 1, \dots, p$, the marginal law of $z$ is $\mathcal N_p(0, V I)$ with $V = A + 1$, and the Bayes rule is $(1 - 1/V) z_i$ ([posterior mean in the normal–normal model](../../bayesian-statistics/empirical-bayes-and-tweedie-s-formula/gaussian-posterior-mean-gaussian-real.md)). Substituting this unbiased estimate of $1/V$ gives the [James–Stein estimator](james-stein.md). This is Efron and Morris's empirical Bayes reading of the James–Stein rule, as stated in Efron (2011), equations (3.7)–(3.9), with $N = p$. The statement covers the unbiasedness; the marginal law of $z$ under the normal–normal model is not part of it.

## Informally uses

- [Mean of the inverse squared norm of a standard Gaussian vector](integral-inv-sum-sq-pi-gaussian-real-zer.md): $\|z\|^2 / V$ is $\chi^2_p$.

## Sources

- B. Efron, "Tweedie's formula and selection bias", *J. Amer. Statist. Assoc.* 106 (2011) 1602–1614. Equation numbers are those of the author's manuscript at https://efron.ckirby.su.domains/papers/2011TweediesFormula.pdf.
- B. Efron, "Empirical Bayes: Concepts and Methods", author's manuscript (2021), https://efron.ckirby.su.domains/papers/2021EB-concepts-methods.pdf. Equations (3.9)–(3.14) give the same argument for the grand-mean variant.

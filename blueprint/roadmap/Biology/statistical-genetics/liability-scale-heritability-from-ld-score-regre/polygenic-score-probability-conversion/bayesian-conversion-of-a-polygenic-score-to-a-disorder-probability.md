# Bayesian conversion of a polygenic score to a disorder probability

**Liability model.** A disorder follows the liability threshold model: liability $L = G + E$ with $G$ and $E$ independent centred Gaussians, $\operatorname{Var}(L) = 1$, and the disorder present ($D = 1$) exactly when $L > t$. The population prevalence is $K = 1 - \Phi(t)$ and $z = \varphi(t)$ is the standard normal density at the threshold. Let the polygenic score $S$ be on the liability scale and well calibrated, $\mathbb{E}[L \mid S] = S$, with $(S, L)$ jointly Gaussian. Then the variance it explains on the liability scale is its own variance,

$$R^2_{\mathrm{liab}} = \frac{\operatorname{Var}(1\cdot S)}{\operatorname{Var}(L)} = \operatorname{Var}(S),$$

which can be computed in a genotyped reference sample with no phenotypes.

**Score distributions in cases and controls.** With $R^2 = R^2_{\mathrm{liab}}$, $i_1 = z/K$ and $i_0 = z/(1-K)$,

$$\mathbb{E}[S \mid D=1] = R^2 i_1, \qquad \operatorname{Var}(S \mid D=1) = R^2\bigl(1 - R^2 i_1(i_1 - t)\bigr),$$

$$\mathbb{E}[S \mid D=0] = -R^2 i_0, \qquad \operatorname{Var}(S \mid D=0) = R^2\bigl(1 - R^2 i_0(i_0 + t)\bigr).$$

When $K < 1/2$ (so $t > 0$), the score has smaller variance in cases than in controls; the variances are equal at $K = 1/2$ and the order reverses for $K > 1/2$. The difference that matters most for rare disorders and well-predicting scores.

**Conversion.** Approximate the conditional laws of $S$ in cases and controls by Gaussians $f_1$, $f_0$ with these moments, and let $\pi$ be a prior disorder probability for the individual (for example the case fraction of the clinical setting, which may exceed $K$). By Bayes' theorem the predicted disorder probability for an individual with score $s$ is

$$\Pr(D = 1 \mid S = s) = \frac{\pi f_1(s)}{\pi f_1(s) + (1-\pi) f_0(s)} .$$

No tuning sample with both genotypes and phenotypes is needed: the inputs are association summary statistics (through a Bayesian polygenic score method), the individual's genotypes, the prevalence $K$, a reference panel and the prior $\pi$.

**Consistency check.** With $\pi = K$ and the exact (truncated, non-Gaussian) conditional laws, the formula reduces to the model probability $\Pr(L > t \mid S = s) = 1 - \Phi\bigl((t - s)/\sqrt{1 - R^2}\bigr)$; the Gaussian approximation of $f_1$ and $f_0$ is accurate for realistic $R^2$.

## Depends on

- [Prevalence of the threshold model](../prevalence.md)
- [Standard normal density at the threshold](../threshold-density.md)
- [Independent Gaussian G and E make G and G + E jointly Gaussian](../has-gaussian-law-liability.md)
- [Calibration slope of a polygenic score](../../genomic-prediction-from-summary-statistics/calib-slope.md)
- [Case indicator of the threshold model](../case-ind.md): the disorder indicator $D = 1\{L > t\}$
- [Bayes' rule for densities](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/bayes-rule/posterior-ae-eq-of-mul-eq.md): the conversion formula from the class densities and the prior $\pi$

## Proof depends on

- [Partial first moment of the liability above the threshold](../integral-mul-case-ind.md): $\mathbb E[L \mid L > t] = z/K$
- [Gaussian conditioning (Schur complement)](../../../../Probability/distributions/continuous/gaussian-conditioning/cond-distrib-multivariate-gaussian.md): $L \mid S = s \sim \mathcal N(s, 1 - R^2)$ in the consistency check

## Expansion

Calibration means the regression of $L$ on $S$ has slope $1$, so $\operatorname{Cov}(S, L) = \operatorname{Var}(S)$ and, conversely, the regression of $S$ on $L$ has slope $R^2$: $S = R^2 L + U$ with $U$ independent of $L$ and $\operatorname{Var}(U) = R^2 - R^4$. For a standard normal $L$ truncated to $L > t$, $\mathbb{E}[L \mid L > t] = z/K$ and $\operatorname{Var}(L \mid L > t) = 1 - (z/K)(z/K - t)$; truncation to $L < t$ gives mean $-z/(1-K)$ and variance $1 - \tfrac{z}{1-K}\bigl(\tfrac{z}{1-K} + t\bigr)$. Hence $\mathbb{E}[S \mid D] = R^2\,\mathbb{E}[L \mid D]$ and $\operatorname{Var}(S \mid D) = R^4\operatorname{Var}(L \mid D) + R^2 - R^4$, which are the stated moments. Bayes' theorem with the two class densities gives the posterior. For the check, calibration and joint Gaussianity give $L \mid S = s \sim \mathcal{N}(s, 1 - R^2)$, so $\Pr(L > t \mid S = s) = 1 - \Phi\bigl((t-s)/\sqrt{1-R^2}\bigr)$, and Bayes' theorem with the exact class densities and prior $K$ returns exactly this conditional probability.

## Sources

- E. Uffelmann et al., "Estimating disorder probability based on polygenic prediction using the BPC approach", Nature Communications (2025), Methods, "Bayesian polygenic score Probability Conversion (BPC) approach", Eqs. 2–3 and Supplementary Note 4 (normal theory for case and control score moments), <https://doi.org/10.1038/s41467-025-62929-x>, PMCID PMC12475198.

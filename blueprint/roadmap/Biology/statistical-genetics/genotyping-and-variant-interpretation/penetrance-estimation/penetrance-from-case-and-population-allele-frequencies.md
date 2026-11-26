# Penetrance from case and population allele frequencies

Let $D$ be the event that an individual has the disease (by a fixed age) and $A$ the event that the individual carries a given risk allele (or any allele in a defined class), in a population where $P(A) > 0$. The penetrance is $P(D \mid A)$. By Bayes' theorem,

$$P(D \mid A) = \frac{P(D)\, P(A \mid D)}{P(A)},$$

that is, penetrance equals prevalence times the carrier frequency among cases divided by the carrier frequency in the population.

**Proposition (plug-in estimator and delta-method interval).** Let $\hat p_D = X_D/n_D$, $\hat q_c = X_c/n_c$ and $\hat q_p = X_p/n_p$ be independent binomial proportions estimating the prevalence $p_D = P(D)$, the case carrier frequency $q_c = P(A\mid D)$ and the population carrier frequency $q_p = P(A)$, all in $(0,1)$. The estimator $\hat\pi = \hat p_D\,\hat q_c/\hat q_p$ satisfies

$$\log\hat\pi = \log\hat p_D + \log\hat q_c - \log\hat q_p,$$

and, as $n_D, n_c, n_p \to \infty$,

$$\operatorname{Var}(\log\hat\pi) \approx \frac{1 - p_D}{n_D\, p_D} + \frac{1 - q_c}{n_c\, q_c} + \frac{1 - q_p}{n_p\, q_p},$$

so that $\exp\bigl(\log\hat\pi \pm z_{1-\alpha/2}\,\widehat{\mathrm{se}}\bigr)$, with the plug-in standard error $\widehat{\mathrm{se}}$, is an asymptotic $1 - \alpha$ confidence interval for $P(D\mid A)$.

## Proof depends on

- [Delta method in one dimension](../../../../Probability/convergence-of-measures/slutsky-s-theorem-and-the-delta-method/delta-method-real.md)

## Expansion

Bayes' theorem gives the identity. For a binomial proportion $\hat q$ with $n$ trials, the delta method applied to $\log$ gives $\operatorname{Var}(\log\hat q) \approx q(1-q)/n \cdot (1/q)^2 = (1-q)/(nq)$; independence of the three samples makes the variances add on the log scale. The estimator needs the case and population cohorts to be ascertained without regard to carrier status, the variant class to be defined identically in both, and $P(D)$ to refer to the same population and age range; if $\hat q_p$ can be $0$ in finite samples, a continuity or degeneracy adjustment is required. McGurk et al. (2023) apply this estimator to rare variants in cardiomyopathy genes, using population-biobank carrier frequencies and published prevalences, with a log-scale delta-method interval.

## Sources

- K. A. McGurk, X. Zhang, P. Theotokis et al., "The penetrance of rare variants in cardiomyopathy-associated genes: a cross-sectional approach to estimating penetrance for secondary findings", The American Journal of Human Genetics 110(9) (2023), 1482–1495, <https://doi.org/10.1016/j.ajhg.2023.08.003>, PMCID PMC10502871 (Statistical analysis: estimation of penetrance and 95% confidence interval).

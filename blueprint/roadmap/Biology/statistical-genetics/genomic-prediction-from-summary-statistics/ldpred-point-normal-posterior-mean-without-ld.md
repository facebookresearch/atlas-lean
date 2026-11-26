# Posterior mean marker effect under a point-normal prior without linkage disequilibrium

Let $M$ standardized, mutually unlinked markers have effects $\beta_1, \dots, \beta_M$ on a standardized phenotype with SNP heritability $h^2 \in (0, 1]$, and let $N$ be the training sample size. Assume:

1. **Point-normal prior.** For a fraction $p \in (0, 1]$ of causal markers, the $\beta_i$ are independent with

$$\beta_i \sim \begin{cases} \mathcal N\!\left(0, \dfrac{h^2}{Mp}\right) & \text{with probability } p, \\[4pt] 0 & \text{with probability } 1 - p. \end{cases}$$

2. **Summary-statistic likelihood.** The marginal least-squares estimate satisfies $\tilde\beta_i \mid \beta_i \sim \mathcal N(\beta_i, 1/N)$, independently over $i$ (the large-$M$ approximation of the variance $(1 - h^2/M)/N$).

Write $\varphi(x; v)$ for the $\mathcal N(0, v)$ density at $x$. Then the posterior probability that marker $i$ is causal is

$$\bar p_i = \frac{p\, \varphi\!\left(\tilde\beta_i; \tfrac{h^2}{Mp} + \tfrac1N\right)}{p\, \varphi\!\left(\tilde\beta_i; \tfrac{h^2}{Mp} + \tfrac1N\right) + (1 - p)\, \varphi\!\left(\tilde\beta_i; \tfrac1N\right)},$$

and the posterior mean effect is

$$\mathbb E(\beta_i \mid \tilde\beta_i) = \frac{1}{1 + \dfrac{Mp}{N h^2}}\; \bar p_i\; \tilde\beta_i .$$

For $p = 1$ this reduces to the uniform infinitesimal shrinkage factor $\left(1 + \frac{M}{N h^2}\right)^{-1}$.

## Depends on

- [Effect-estimate model for polygenic score accuracy](prsmodel.md)

## Expansion

Marginally, $\tilde\beta_i$ is a two-component normal mixture with variances $h^2/(Mp) + 1/N$ (slab) and $1/N$ (spike), which gives $\bar p_i$ by Bayes' rule (the paper's Equation A1). Conditional on the slab, the normal-normal update gives $\beta_i \mid \tilde\beta_i \sim \mathcal N\big(k\tilde\beta_i, k/N\big)$ with $k = \frac{h^2/(Mp)}{h^2/(Mp) + 1/N} = \big(1 + \frac{Mp}{Nh^2}\big)^{-1}$; conditional on the spike the posterior is the point mass at $0$. Averaging the two conditional means with weights $\bar p_i$ and $1 - \bar p_i$ gives the formula. The authors call this unlinked-marker shrinkage "Bpred"; LDpred replaces it by a Gibbs sampler when markers are in LD.

## Sources

- B. J. Vilhjálmsson, J. Yang, H. K. Finucane, et al., "Modeling Linkage Disequilibrium Increases Accuracy of Polygenic Risk Scores", American Journal of Human Genetics 97 (2015), 576–592, <https://doi.org/10.1016/j.ajhg.2015.09.001> (PMC4596916). Appendix A.

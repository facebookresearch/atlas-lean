# Coheterogeneity of pleiotropic deviations between two outcomes

**Setting.** Selected genetic instruments $k \in \mathcal{K}$ ($K = |\mathcal{K}|$) for an exposure $X$ give ratio estimates for two outcome traits $Y_1, Y_2$ with the decomposition

$$\hat\theta_{l,k} = \theta_l + \alpha_{l,k} + \epsilon_{l,k}, \qquad l = 1,2,$$

where $\theta_l$ is the causal effect of $X$ on $Y_l$, $\alpha_{l,k}$ the pleiotropic bias of instrument $k$, and $\epsilon_{l,k}$ mean-zero sampling error with variance $\sigma^2_{l,k}$. With weights $w_k \propto (\sigma^2_{1,k}\sigma^2_{2,k})^{-1/2}$, $\sum_k w_k = 1$, and centred biases $\tilde\alpha_{l,k} = \alpha_{l,k} - \sum_j w_j\alpha_{l,j}$, the **coheterogeneity** is the weighted correlation

$$\rho_{CH} = \frac{C_{12}}{\tau_1\tau_2}, \qquad C_{12} = \sum_k w_k\tilde\alpha_{1,k}\tilde\alpha_{2,k}, \qquad \tau_l^2 = \sum_k w_k\tilde\alpha_{l,k}^2 .$$

Its summary-statistic estimator uses estimated weights $\hat w_k$, deviations $\Delta_{l,k} = \hat\theta_{l,k} - \sum_j\hat w_j\hat\theta_{l,j}$, and an estimate $\hat\sigma_{12,k}$ of $\operatorname{Cov}(\epsilon_{1,k},\epsilon_{2,k})$ (e.g. from bivariate LD-score regression):

$$\hat C_{12} = \sum_k \hat w_k\big(\Delta_{1,k}\Delta_{2,k} - \hat\sigma_{12,k}\big), \qquad \hat\tau_l^2 = \Big[\sum_k\hat w_k\big(\Delta^2_{l,k} - \hat\sigma^2_{l,k}\big)\Big]_+, \qquad \hat\rho_{CH} = \frac{\hat C_{12}}{\hat\tau_1\hat\tau_2}.$$

**Theorem (consistency and asymptotic normality).** Under regularity conditions (bounded weights $\max_k w_k = O(1/K)$, strong instruments, smoothness of the map from summary statistics to $\hat\rho_{CH}$), as the GWAS sample size $N \to \infty$ with $K = K_N \to \infty$, $\hat\rho_{CH} - \rho_{CH} \to 0$ in probability and

$$\sqrt{N K_N}\,\big(\hat\rho_{CH} - \rho_{CH}\big) \xrightarrow{d} \mathcal{N}(0, \sigma^{*2}),$$

with $\sigma^{*2}$ the limit of $K_N$ times a delta-method variance built from the per-instrument covariance matrices of the GWAS estimates.

**Lemma (link to shared invalid instruments).** Suppose a fraction $\pi$ of the instruments is valid and the invalid fraction $1 - \pi$ splits into proportions $q_0$ (invalid through a confounder shared by $Y_1$ and $Y_2$), $q_1$ ($Y_1$-specific) and $q_2$ ($Y_2$-specific). Under a random-effects model for SNP effects, $\rho_{CH}$ converges to

$$\frac{(1-\pi)\,q_0\,ab}{\sqrt{\big[c^2 + (1-\pi)(q_0 + q_1)a^2\big]\big[d^2 + (1-\pi)(q_0 + q_2)b^2\big]}}$$

for constants $a,b,c,d$ determined by the variance components and confounder effects. Thus $\rho_{CH}$ is monotone in the overlap $q_0$, increasing or decreasing as the shared confounder acts on the two outcomes in the same or opposite directions, which makes it a criterion for choosing auxiliary traits from which to borrow instrument-validity information.

## Depends on

- [Generalized plurality and majority rules for multiple exposures](generalized-plurality-and-majority-rules-for-multiple-exposures.md)

## Expansion

The correction terms $\hat\sigma_{12,k}$ and $\hat\sigma^2_{l,k}$ remove the sampling-error contribution to the empirical cross-moment and variances, in the spirit of the DerSimonian–Laird heterogeneity estimator, so that $\hat C_{12}$ and $\hat\tau_l^2$ target the pleiotropic components. $\hat\rho_{CH}$ is a smooth function of the stacked per-instrument summary statistics with $O(1/K)$ weights, so a delta-method expansion around the population values and a Lindeberg central limit theorem across instruments give the $\sqrt{NK}$ rate. In the random-effects model only shared-confounder instruments contribute to the cross-moment, while all invalid instruments of each trait contribute to its variance, producing the stated ratio.

## Sources

- Anagh Chattopadhyay, Nilanjan Chatterjee, "Improving Mendelian Randomization Analysis by Instrument Borrowing from Auxiliary Outcome Traits", arXiv (2026). Methods (coheterogeneity measure and estimator), Theorem 1, Lemma 1, Appendix A (conditions, Lemma 2). <https://doi.org/10.48550/arXiv.2607.16086>

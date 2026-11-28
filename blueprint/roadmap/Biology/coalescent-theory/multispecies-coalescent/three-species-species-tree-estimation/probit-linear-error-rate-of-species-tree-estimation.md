# Probit-linear error rate of species-tree estimation

**Setting.** Many species-tree estimators for three species pick the tree whose per-locus score has the largest sample mean. Let $z_i = (z_{i1}, z_{i2}, z_{i3})^{\mathsf T}$, $i = 1, \dots, m$, be i.i.d. per-locus scores for the true tree and the two alternatives, with mean $\mu = (\mu_1, \mu_2, \mu_2)^{\mathsf T}$, $\Delta\mu = \mu_1 - \mu_2 > 0$, and covariance $\Sigma = (\sigma_{jk})$ with $\sigma_{11} = \sigma_1^2$, $\sigma_{12} = \sigma_{13} = \rho_{12}\sigma_1\sigma_2$, $\sigma_{22} = \sigma_{33} = \sigma_2^2$, $\sigma_{23} = \rho_{23}\sigma_2^2$. Let $\bar z = m^{-1}\sum_i z_i$, so $\bar z \approx \mathcal N_3(\mu, \Sigma/m)$ for large $m$.

**Theorem.** Let $\zeta = \Pr\{\bar z_1 < \max(\bar z_2, \bar z_3)\}$ be the error probability.

1. (Normal approximation.) For large $m$,

$$\zeta \approx \Phi\!\left(\frac{-\Delta\mu\sqrt m + \sqrt{\tfrac{1}{\pi}(\sigma_2^2 - \sigma_{23})}}{\sqrt{\sigma_1^2 - 2\sigma_{12} + \sigma_2^2 - \tfrac1\pi(\sigma_2^2 - \sigma_{23})}}\right),$$

where $\Phi$ is the standard normal distribution function. This is an approximation, not a bound; the source uses it for finite-$m$ calculations.

2. (Bounds.) Treat $\bar z \sim \mathcal N_3(\mu, \Sigma/m)$ as exact. Let $s_1^2 = \sigma_1^2 - 2\sigma_{12} + \sigma_2^2 - \tfrac12(\sigma_2^2 - \sigma_{23})$ and $s_2^2 = \tfrac12(\sigma_2^2 - \sigma_{23})$ with $s_1 > 0$, and put $a = s_2/s_1$, $b = \Delta\mu\sqrt m/s_1$ and $h = b/\sqrt{1 + a^2}$. Then

$$\Phi(-h)\Big(1 + \tfrac{2}{\pi}\tan^{-1} a\Big) \le \zeta < 2\Phi(-h) = \Phi\Big(-h + \tfrac{\log 2}{h} + o\big(\tfrac1h\big)\Big).$$

Consequently $-h \le \Phi^{-1}(\zeta) < -h + \log 2/h + o(1/h)$. Since $s_1^2 + s_2^2 = \sigma_1^2 - 2\sigma_{12} + \sigma_2^2$, we have $h = \Delta\mu\sqrt m/\sqrt{\sigma_1^2 - 2\sigma_{12} + \sigma_2^2}$, so as $m \to \infty$ the probit $\Phi^{-1}(\zeta)$ of the species-tree error rate decreases linearly in $\sqrt m$ with asymptotic slope $-\Delta\mu/\sqrt{\sigma_1^2 - 2\sigma_{12} + \sigma_2^2}$, which comes from these bounds and not from the approximation in item 1. Applied to multinomial site-pattern counts, the approximation in item 1 gives the error rates of concatenation and isml.

## Depends on

- [Independent-sites likelihood selects the majority site pattern](independent-sites-likelihood-selects-the-majority-site-pattern.md)

## Proof depends on

Its proof is that of the source below, as the Expansion describes.

## Expansion

Approximate $\max(\bar z_2, \bar z_3)$ by a normal variable with Clark's moments for the maximum of two exchangeable correlated normals: its mean exceeds $\mu_2$ by $\sqrt{(\sigma_2^2 - \sigma_{23})/(\pi m)}$ and its variance and covariance with $\bar z_1$ follow from the same formulas. Then $\bar z_1 - \max(\bar z_2, \bar z_3)$ is approximately normal and $\zeta$ is its probability of being negative; this heuristic gives item 1 only. Item 2 is proved separately in the source's Appendix A, where tighter bounds are also derived; the lower bound gives $\Phi^{-1}(\zeta) \ge -h$, and the upper bound $2\Phi(-h)$, rewritten with the normal tail asymptotics, gives $\Phi^{-1}(\zeta) < -h + O(1/h)$.

## Sources

- T. Zhu and Z. Yang, "Complexity of the simplest species tree problem", *Molecular Biology and Evolution* (2021), Theorem 1 (Eqs. 6–7), the remark following it, Corollary 2 (Eq. 8) and Appendix A. <https://doi.org/10.1093/molbev/msab009> (PMC8382899)

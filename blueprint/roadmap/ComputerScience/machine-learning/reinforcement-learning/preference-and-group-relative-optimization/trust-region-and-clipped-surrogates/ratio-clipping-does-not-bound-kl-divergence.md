# Ratio clipping does not bound the KL divergence

Keeping the probability ratio of the sampled action inside the PPO clipping range does not bound the KL divergence between the old and new action distributions at that state: over the set of parameters satisfying the ratio constraint, the divergence is unbounded.

Fix a state $s_t$, a sampled action $a_t$, a clipping parameter $\epsilon \in (0,1)$ and an old parameter $\theta_{\mathrm{old}}$, and let $r_t(\theta) = \pi_\theta(a_t \mid s_t)/\pi_{\theta_{\mathrm{old}}}(a_t \mid s_t)$ be the ratio of the [PPO clipped surrogate](ppo-clipped-surrogate-objective.md). Let

$$\Theta = \{\theta : 1 - \epsilon \le r_t(\theta) \le 1 + \epsilon\}.$$

1. Discrete actions: if $|A| \ge 3$ and, as $\theta$ varies, $\pi_\theta(\cdot \mid s_t)$ ranges over all probability vectors on $A$ with positive entries, then $\sup_{\theta \in \Theta} \mathrm{KL}\bigl(\pi_{\theta_{\mathrm{old}}}(\cdot \mid s_t) \,\|\, \pi_\theta(\cdot \mid s_t)\bigr) = +\infty$.
2. Gaussian policies: if $A = \mathbb{R}^D$, $\pi_\theta(\cdot \mid s_t) = \mathcal{N}(\mu_\theta(s_t), \Sigma_\theta(s_t))$ and $(\mu_\theta(s_t), \Sigma_\theta(s_t))$ ranges over all pairs of a mean in $\mathbb{R}^D$ and a symmetric positive definite $D \times D$ matrix (the source writes semidefinite; a Lebesgue density, and hence the ratio $r_t$, exists only for definite covariance), then the same supremum is $+\infty$.

## Depends on

- [PPO clipped surrogate objective](ppo-clipped-surrogate-objective.md)

## Proof depends on

- [Kullback-Leibler divergence between multivariate Gaussians](../../../../../InformationTheory/not-yet-classified/part-01/vector-gaussian-kl/kl-div-multivariate-gaussian.md)

## Expansion

The constraint involves only the density of the one sampled action. In the discrete case keep $\pi_\theta(a_t \mid s_t) = \pi_{\theta_{\mathrm{old}}}(a_t \mid s_t)$, so $r_t(\theta) = 1$, and move the mass of a second action $a'$, which the old policy charges, to a third action; as $\pi_\theta(a' \mid s_t) \to 0$ the term $\pi_{\theta_{\mathrm{old}}}(a' \mid s_t) \log(\pi_{\theta_{\mathrm{old}}}(a' \mid s_t)/\pi_\theta(a' \mid s_t))$ diverges while the other terms stay bounded below. With two actions the ratio at $a_t$ fixes the whole distribution, which is why three are needed. In the Gaussian case the density at $a_t$ can be held fixed while the divergence, given by the closed form $\frac12\bigl(\ln(\det \Sigma/\det \Sigma_{\mathrm{old}}) - D + \operatorname{tr}(\Sigma^{-1}\Sigma_{\mathrm{old}}) + (\mu - \mu_{\mathrm{old}})^\top \Sigma^{-1}(\mu - \mu_{\mathrm{old}})\bigr)$ for $\mathrm{KL}(\mathcal{N}(\mu_{\mathrm{old}}, \Sigma_{\mathrm{old}}) \,\|\, \mathcal{N}(\mu, \Sigma))$, grows without bound: for instance take $\Sigma = s^2 I$ with $s \to 0$ and move $\mu$ toward $a_t$ so that the density at $a_t$ stays equal to its old value, which is possible because the peak density $(2\pi s^2)^{-D/2}$ tends to infinity; then $\operatorname{tr}(\Sigma^{-1}\Sigma_{\mathrm{old}}) = \operatorname{tr}(\Sigma_{\mathrm{old}})/s^2$ dominates the logarithmic term and the divergence tends to infinity.

So bounding probability ratios at sampled actions and bounding the KL divergence are different constraints: clipping does not by itself enforce the trust region that underlies the [trust-region policy improvement bound](trust-region-policy-improvement-bound.md). Wang, He and Tan also report ratios far outside the clipping range in practice.

## Sources

- Y. Wang, H. He and X. Tan, *Truly Proximal Policy Optimization*, Proceedings of the 35th Conference on Uncertainty in Artificial Intelligence (UAI 2019), PMLR 115, Theorem 3 and the surrounding discussion (Section 4, Question 2, and Figure 1), with the notation of Section 3. [publisher page](https://proceedings.mlr.press/v115/wang20b.html)

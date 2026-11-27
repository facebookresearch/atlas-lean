# GRPO policy improvement lower bound

For rewards in $[0,1]$, the gain in expected reward of a candidate policy over the current one is at least its importance-weighted group-relative advantage under a sampling policy, minus total variation penalties whose weight grows as the reward variance under the sampling policy shrinks.

Let $\rho_X$ be a distribution on a measurable space of prompts, $Y$ a measurable space of responses, $r$ a reward with $0 \le r(x,y) \le 1$, and $0 < \varepsilon \le 3/4$. Let $\pi_k$ (current), $\alpha$ (sampling) and $\pi$ (candidate) be policies with $\pi(\cdot \mid x)$ absolutely continuous with respect to $\alpha(\cdot \mid x)$. The ratio $\pi(y\mid x)/\alpha(y\mid x)$ below denotes a Radon–Nikodym derivative $d\pi(\cdot\mid x)/d\alpha(\cdot\mid x)$, not a quotient of point masses on a nonatomic response space. Assume the scalar functions of $x$ appearing in the averaged bound below are measurable. With $J(\pi(\cdot \mid x)) = \mathbb{E}_{y \sim \pi(\cdot \mid x)} r(x,y)$, the population [group-relative advantage](group-relative-advantage.md) $A_\alpha$ and its normalizer $\sigma_{\alpha,r,\varepsilon}$, put

$$L_\alpha(\pi(\cdot \mid x)) = \mathbb{E}_{y \sim \alpha(\cdot \mid x)}\Bigl[\frac{\pi(y \mid x)}{\alpha(y \mid x)} A_\alpha(x,y)\Bigr].$$

Then for $\rho_X$-almost every $x$, with $\mathrm{TV}(m_1, m_2) = \sup_B |m_1(B) - m_2(B)|$, which equals the source's $\frac12 \int |f_1 - f_2| \, d\lambda$ for densities $f_1, f_2$ of $m_1, m_2$ with respect to any common dominating measure $\lambda$,

$$J(\pi(\cdot \mid x)) - J(\pi_k(\cdot \mid x)) \ge L_\alpha(\pi(\cdot \mid x)) - 2\, \frac{1 - \sigma_{\alpha,r,\varepsilon}(x)}{\sigma_{\alpha,r,\varepsilon}(x)}\, \mathrm{TV}\bigl(\pi(\cdot \mid x), \alpha(\cdot \mid x)\bigr) - 2\, \mathrm{TV}\bigl(\pi_k(\cdot \mid x), \alpha(\cdot \mid x)\bigr).$$

In the on-policy case $\alpha = \pi_k$ the last term vanishes: $J(\pi(\cdot \mid x)) - J(\pi_k(\cdot \mid x)) \ge L_{\pi_k}(\pi(\cdot \mid x)) - 2\,\frac{1 - \sigma_{\pi_k,r,\varepsilon}(x)}{\sigma_{\pi_k,r,\varepsilon}(x)}\, \mathrm{TV}(\pi(\cdot \mid x), \pi_k(\cdot \mid x))$. Averaging over prompts and applying the Cauchy–Schwarz inequality,

$$\mathbb{E}_{x} J(\pi(\cdot \mid x)) - \mathbb{E}_{x} J(\pi_k(\cdot \mid x)) \ge \mathbb{E}_{x} L_\alpha(\pi(\cdot \mid x)) - 2 M_{\alpha,r,\varepsilon} \bigl(\mathbb{E}_{x} \mathrm{TV}^2(\pi(\cdot \mid x), \alpha(\cdot \mid x))\bigr)^{1/2} - 2\, \mathbb{E}_{x} \mathrm{TV}(\pi_k(\cdot \mid x), \alpha(\cdot \mid x)),$$

where $x \sim \rho_X$ and $M_{\alpha,r,\varepsilon} = \bigl(\mathbb{E}_{x}\, (1 - \sigma_{\alpha,r,\varepsilon}(x))^2/\sigma_{\alpha,r,\varepsilon}(x)^2\bigr)^{1/2}$.

## Depends on

- [Group-relative advantage](group-relative-advantage.md)
- [Total variation distance between finite measures](../../../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)
- [Total variation norm is twice the supremum over events](../../../../../InformationTheory/information-inequalities/total-variation-and-pinsker-s-inequality/tv-dist-eq-two-mul-total-variation-dist.md)

## Proof depends on

- [Change of measure for importance weights](../../../bayesian-inference-and-sampling/monte-carlo-and-importance-sampling/integral-weight-mul.md)
- [Hölder's inequality for functions with values in [0, ∞]](../../../../../MeasureTheory/lp-spaces/h-lder-and-minkowski-inequalities-for-integrals/h-lder-s-inequality/lintegral-mul-le-lp-mul-lq.md)

## Expansion

Absolute continuity gives $L_\alpha(\pi) = \mathbb{E}_{y \sim \pi}[A_\alpha(x,y)] = (J(\pi) - J(\alpha))/\sigma_{\alpha,r,\varepsilon}(x)$, hence

$$L_\alpha(\pi) - \bigl(J(\pi) - J(\pi_k)\bigr) = \frac{1 - \sigma_{\alpha,r,\varepsilon}}{\sigma_{\alpha,r,\varepsilon}} \bigl(J(\pi) - J(\alpha)\bigr) + \bigl(J(\pi_k) - J(\alpha)\bigr).$$

The first identity is the change of measure $\int (\pi/\alpha) A_\alpha \, d\alpha = \int A_\alpha \, d\pi$ for the density $\pi/\alpha$. The proof also needs, for a bounded measurable $g$, the bound $\mathbb{E}_{m_1} g - \mathbb{E}_{m_2} g \le 2\|g\|_\infty \mathrm{TV}(m_1, m_2)$ with $\mathrm{TV}(m_1, m_2) = \frac12 \int |m_1 - m_2|$, the variational form of total variation that the source states as its Lemma 1 (Appendix C); it follows by writing the difference as $\int g \, (dm_1 - dm_2)$ and bounding $|g|$ by $\|g\|_\infty$, and no statement page for it is linked here. The averaged bound uses Hölder's inequality with exponents $2$ and $2$ (the Cauchy–Schwarz inequality) for the nonnegative functions $x \mapsto (1 - \sigma_{\alpha,r,\varepsilon}(x))/\sigma_{\alpha,r,\varepsilon}(x)$ and $x \mapsto \mathrm{TV}(\pi(\cdot \mid x), \alpha(\cdot \mid x))$ under $\rho_X$. The coefficient $(1 - \sigma_{\alpha,r,\varepsilon})/\sigma_{\alpha,r,\varepsilon}$ is nonnegative because a reward in $[0,1]$ has variance at most $1/4$, so $\sigma_{\alpha,r,\varepsilon} \le \sqrt{1/4 + \varepsilon} \le 1$ when $\varepsilon \le 3/4$; this is where the restriction on $\varepsilon$ enters. Bounding both differences gives the per-prompt bound. The proof uses the closed form of the advantage and no Markov decision process structure.

What the bound covers: the mean and variance are the exact population statistics under $\alpha$, not group estimates; $L_\alpha$ is the unclipped importance-weighted advantage, without the clipping and without the KL penalty of the [GRPO clipped objective](grpo-clipped-surrogate-objective.md); and the per-prompt weight depends on the data. For a binary verifiable reward with success probability $p$ under $\alpha$, the weight is $(1 - \sqrt{p(1-p) + \varepsilon})/\sqrt{p(1-p) + \varepsilon}$, large when $p$ is near $0$ or $1$, so the bound is weak for prompts that the sampling policy always or never solves; Mroueh et al. relate this to filtering or masking such prompts. Through Pinsker's inequality the bound motivates a KL-constrained, and then clipped, surrogate, but the clipped surrogate is a practical relaxation that the theorem does not cover. Compared with the [trust-region policy improvement bound](../trust-region-and-clipped-surrogates/trust-region-policy-improvement-bound.md), the weights of the total variation terms are policy- and data-dependent rather than absolute constants.

The source states the definitions with $0 < \varepsilon < 1$ and the on-policy corollary with $\varepsilon \le 3/4$; its proof of the general bound uses $\sigma_{\alpha,r,\varepsilon} \le 1$, which the restriction $\varepsilon \le 3/4$ guarantees. The importance-sampling identity requires $\pi(\cdot \mid x)$ to be absolutely continuous with respect to $\alpha(\cdot \mid x)$, which the source uses without stating. The prompt-measurability assumption makes the averaged expression well-defined: its scalar integrands are bounded because $0\le r\le1$, $\sigma_{\alpha,r,\varepsilon}\ge\sqrt\varepsilon$ and total variation between probability measures is at most $1$. No measurability of an uncountable supremum is inferred merely from the pointwise policy notation.

## Sources

- Y. Mroueh, N. Dupuis, B. Belgodere, A. Nitsure, M. Rigotti, K. Greenewald, J. Navratil, J. Ross and J. Rios, *Revisiting Group Relative Policy Optimization: Insights into On-Policy and Off-Policy Training*, International Conference on Learning Representations (ICLR 2026), Theorem 1, Corollary 1 and equation (4) (Section 3.1), the interpretation of the bound for verifiable rewards, Section 3.2, and the proof in Appendix C (with its Lemma 1). [PDF](https://proceedings.iclr.cc/paper_files/paper/2026/file/b4008025c2182bfe16fcc8566ee14d64-Paper-Conference.pdf)

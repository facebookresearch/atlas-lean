# Unbiased likelihood estimator for the Wright–Fisher diffusion

**Setting.** Allele frequencies follow the Wright–Fisher diffusion

$$
dX_t = \gamma(X_t, \vartheta)\,dt + \sqrt{X_t(1 - X_t)}\,dB_t, \qquad X_0 = x_0 \in [0,1],
$$

with unknown parameter $\vartheta \in \Theta$, observed at discrete times, where $\Theta \subset \mathbb{R}^d$ is compact and contains the maximum likelihood estimator. The drift has the form

$$
\gamma(x,\vartheta) = \alpha(x) + x(1-x)\,\eta(x;\vartheta), \qquad \alpha(x) = \tfrac12\big(\theta_a - (\theta_a + \theta_A)x\big),
$$

with fixed mutation rates $\theta_a, \theta_A > 0$ and a selection function $\eta(\cdot;\vartheta) \in C^1[0,1]$ for every $\vartheta \in \Theta$, with $\eta(x;\cdot)$ continuous on $\Theta$ for every $x \in [0,1]$. Let $X^\alpha$ be the reference neutral Wright–Fisher diffusion with mutation (drift $\alpha$, i.e. $\eta \equiv 0$), with transition density $p(x, y, t)$. The change of drift from $X^\alpha$ to $X$ is governed, via Girsanov's theorem and Itô's formula, by the potential and the rate function

$$
A(x;\vartheta) = \int_0^x \eta(z;\vartheta)\,dz, \qquad \phi(x;\vartheta) = \tfrac12\Big[x(1-x)\big(\eta^2(x;\vartheta) + \eta'(x;\vartheta)\big) + 2\eta(x;\vartheta)\,\alpha(x)\Big],
$$

where $A(x;\cdot)$ is continuous on $\Theta$, and $\phi$ is continuous in $x$ with bounds $\phi^-(\vartheta) \le \phi(x;\vartheta) \le \phi^+(\vartheta)$ for all $x \in [0,1]$, $\vartheta \in \Theta$, with $\phi^-$ and $\phi^+$ continuous on $\Theta$.

**Results.**

1. *(Bridge representation.)* The transition density of $X$ is

    $$
    p_\vartheta(x, y; t) = p(x, y, t)\,\exp\{A(y;\vartheta) - A(x;\vartheta) - t\phi^-(\vartheta)\}\; a(x, y; \vartheta),
    $$

    $$
    a(x, y;\vartheta) = \mathbb{E}_{\mathbb{WF}^{t,x,y}}\Bigl[\exp\Bigl\{-\int_0^t \bigl(\phi(\omega_s;\vartheta) - \phi^-(\vartheta)\bigr)\,ds\Bigr\}\Bigr],
    $$

    where the expectation is over bridges $\omega$ of the reference process from $x$ to $y$ in time $t$.

2. *(Unbiased estimator.)* There is a random element $\Lambda$, independent of $\vartheta$ (a random truncation level for the series of $p$, a Poisson point set for the exponential of the integral, and bridge skeleton points), and a likelihood contribution $L(\Lambda, \vartheta) = \exp\{A(y;\vartheta) - A(x;\vartheta) - t\phi^-(\vartheta)\}\,\Pi(\Lambda, x, y; \vartheta)$, a.s. continuous in $\vartheta$, with $\mathbb{E}[L(\Lambda,\vartheta)] = p_\vartheta(x,y;t)$; the full likelihood is the product over observation intervals.
3. *(Uniform consistency.)* For i.i.d. copies $\Lambda^1, \Lambda^2, \dots$,

    $$
    \lim_{N\to\infty}\sup_{\vartheta \in \Theta}\Bigl|\frac1N\sum_{j=1}^{N} L(\Lambda^j, \vartheta) - L(\vartheta)\Bigr| = 0 \quad\text{a.s.},
    $$

    and any sequence of maximizers of the Monte Carlo likelihood converges to the maximum likelihood estimator whenever the latter is unique.

## Depends on

- [Wright–Fisher generator with two-way mutation](../../wright-fisher-diffusion-with-mutation/mutation-generator.md)
- [Jacobi series of the Wright–Fisher transition density with mutation](../jacobi-series-of-the-mutation-transition-density.md)

## Expansion

The Wright–Fisher transition density has no closed form under selection, but the neutral density with mutation has an explicit eigenfunction (or coalescent-mixture) series that can be sampled exactly. Girsanov's formula expresses the selected law as a reweighting of the neutral bridge; because $\phi$ is bounded below on $[0,1]$, the bridge expectation $a$ is the probability that a Poisson process of rate $\phi - \phi^-$ under the bridge has no points of a certain kind, which can be estimated without bias from finitely many bridge evaluations. Fixing $\Lambda$ and varying $\vartheta$ gives a smooth random likelihood surface, and a uniform strong law of large numbers in the Banach space of continuous functions on $\Theta$ gives consistency of the simulated maximum likelihood estimator.

## Sources

- Celia García-Pareja and Fabio Nobile, "Unbiased Likelihood Estimation of Wright–Fisher Diffusion Processes", in *Monte Carlo and Quasi-Monte Carlo Methods*, Springer Proceedings in Mathematics & Statistics (2024), 259–275, <https://doi.org/10.1007/978-3-031-59762-6_12>. Numbering as in the preprint arXiv:2303.05390v2, <https://arxiv.org/abs/2303.05390v2>: Lemma 1, Section 3 (likelihood contribution $L(\Lambda,\vartheta)$), Theorem 1, Corollaries 1–2.

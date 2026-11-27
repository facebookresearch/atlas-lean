# Aitchison diffusion: Brownian motion on the simplex as neutral stochastic replicator dynamics

**Aitchison geometry.** On the open simplex $\Delta = \{p \in \mathbb{R}^n : p_i > 0, \sum_i p_i = 1\}$ of type frequencies, with closure $\mathcal{C}(x) = x/\sum_i x_i$, define perturbation $p \oplus q = \mathcal{C}(p_1q_1,\dots,p_nq_n)$, powering $\alpha \odot p = \mathcal{C}(p_1^\alpha,\dots,p_n^\alpha)$, and the inner product

$$ \langle p,q\rangle_A = \frac{1}{2n}\sum_{i,j=1}^n \ln\frac{p_i}{p_j}\ln\frac{q_i}{q_j} . $$

Then $(\Delta,\oplus,\odot,\langle\cdot,\cdot\rangle_A)$ is an $(n-1)$-dimensional Hilbert space, isometric to $\mathbb{R}^{n-1}$ through the isometric log-ratio map, and its metric $d_A$ induces the Euclidean topology on $\Delta$. Let $\lambda_A$ denote the Aitchison (Lebesgue) measure.

**Theorem (Brownian motion on $\Delta$).** For every $T > 0$ the Stratonovich SDE

$$ dX^i_t = X^i_t\Big(\circ dB^i_t - \sum_{j=1}^n X^j_t\circ dB^j_t\Big), \qquad i = 1,\dots,n, \qquad X_0 = p \in \Delta, $$

driven by independent Brownian motions $B^1,\dots,B^n$, has a unique $\Delta$-valued solution, and $X$ is a Brownian motion of the Hilbert space $(\Delta,\oplus)$: it has $\oplus$-independent stationary increments, continuous paths, and Gaussian increments with identity covariance in Aitchison coordinates. Consequently:
1. $\lambda_A$ is invariant and reversible, and the transition density with respect to $\lambda_A$ is the Gaussian kernel $p_t(p,q) = (2\pi t)^{-(n-1)/2}\exp\big(-\|p\ominus q\|_A^2/2t\big)$; $d_A$ is the intrinsic metric and $\lim_{t\downarrow 0} t\ln p_t(p,q) = -d_A^2(p,q)/2$.
2. (Wong–Zakai type) For $\lambda > 0$, let $y = y^{(\lambda)}$ solve the $n$-dimensional Ornstein–Uhlenbeck SDE $\lambda^2\,dy_t = -y_t\,dt + \lambda\,dB_t$ with $y_0 \sim N(0, I)$ and $B$ an $n$-dimensional Brownian motion independent of $p(0)$. Then the replicator equation $\dot p_i = \lambda^{-1}p_i(y^i_t - \bar y_t)$, with mean fitness $\bar y_t = \sum_i p_iy^i_t$, has a unique solution $p^\lambda$, and $p^\lambda \Rightarrow X$ weakly as $\lambda \to 0$.
3. (Donsker type) A random walk $p^{(k)} = p^{(k-1)}\oplus f_{(k)}$ with i.i.d. steps of centered log-ratios and identity log-ratio covariance, rescaled as $n^{-1/2}\odot p_{nt}$, converges weakly to $X$ started at the barycenter.
4. (JKO) For $\mu_0 \in \mathcal{P}_2(\Delta)$ with finite relative entropy $\mathcal{S}_A(\mu) = \int \ln\frac{d\mu}{d\lambda_A}\,d\mu$ ($+\infty$ unless $\mu \ll \lambda_A$), the law $\mu_t$ of $X_t$ is the limit $\mu_t = \lim_{n \to \infty} (K_{t/n})^n[\mu_0]$, where $K_h[\mu]$ minimizes $\bar\mu \mapsto \mathcal{S}_A(\bar\mu) + \frac{1}{2h} W_A^2(\bar\mu, \mu)$ over $\mathcal{P}_2(\Delta)$ and $W_A$ is the Wasserstein distance for $d_A$; its density solves the heat equation of the Aitchison geometry.

Neutral evolution of type frequencies under purely random selection is therefore Brownian motion in the log-ratio geometry. This differs from Wright–Fisher genetic drift, whose diffusion lives on the Euclidean simplex with variance $p_i(\delta_{ij} - p_j)$.

## Depends on

- [Closure of a positive composition to total one](../../../../Probability/linear-models-multivariate/centred-log-ratio-transform-of-compositional-dat/closure-op.md)
- [Centred log-ratio transform of a positive composition](../../../../Probability/linear-models-multivariate/centred-log-ratio-transform-of-compositional-dat/clr.md)
- [Squared Aitchison distance](../../../../Probability/linear-models-multivariate/centred-log-ratio-transform-of-compositional-dat/aitchison-dist-sq.md)

- [Multidimensional Brownian motion](../../../../Probability/stochastic-calculus/construction-and-sample-paths-of-brownian-motion/multidimensional-brownian-motion.md)
- [Solution of the replicator equation](../../../population-dynamics/replicator-dynamics/is-solution.md)

## Proof depends on

## Expansion

In centered log-ratio coordinates $\mathrm{clr}(p)_i = \ln p_i - \frac1n\sum_j\ln p_j$, the Stratonovich chain rule turns the SDE into $d\,\mathrm{clr}(X)_t = (I - \frac1n\mathbf{1}\mathbf{1}^{\mathsf T})\,dB_t$, a standard Brownian motion on the hyperplane $\sum_i x_i = 0$. Every claim follows by transporting Euclidean facts through this isometry: the Gaussian heat kernel, Varadhan asymptotics, the classical Wong–Zakai and Donsker theorems, and the Jordan–Kinderlehrer–Otto characterization of the heat flow as the Wasserstein gradient flow of entropy.

## Sources

- Tobias Lehmann, "Darwinian evolution as Brownian motion on the simplex: A geometric perspective on stochastic replicator dynamics", arXiv:2008.05410 (2020), Theorem 1, Lemma 2, Theorem 4, Corollary 6, Theorems 7, 8 and 9, <https://doi.org/10.48550/arXiv.2008.05410>; published in *Annals of Applied Probability* 33(1) (2023) 344–375, <https://doi.org/10.1214/22-AAP1817>. Locators follow arXiv v1 (arXiv v1 Theorem 9 prints a minus sign before the Wasserstein cost in the JKO functional; item 4 states the standard plus sign).

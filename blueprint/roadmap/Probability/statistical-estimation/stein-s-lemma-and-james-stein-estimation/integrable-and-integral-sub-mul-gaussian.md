# Stein's lemma

Let $\mu \in \mathbb R$, $v \ge 0$, $X \sim \mathcal N(\mu, v)$, and let $g : \mathbb R \to \mathbb R$ be differentiable at every point, with derivative $g'$ such that $g'(X)$ is integrable. Then $(X - \mu)\, g(X)$ is integrable and

$$\mathbb E[(X - \mu)\, g(X)] = v\, \mathbb E[g'(X)] .$$

For $v = 0$ both sides vanish. This is Gaussian integration by parts: $\varphi_v'(t) = -\frac{t}{v} \varphi_v(t)$ for the $\mathcal N(0, v)$ density. Johnstone's draft writes the identity for $\mathcal N(0, 1)$ in Section 2.6, just before equation (2.58), and states it under weak differentiability (absolute continuity); the statement above asks for differentiability everywhere, which covers $C^1$ functions but not, for example, $g(x) = |x|$. Integrability of $(X - \mu) g(X)$ is part of the conclusion, not a hypothesis.

## Background

- [Stein's lemma in Lande's form](../../../Biology/quantitative-genetics/lande-s-selection-gradient/integral-sub-mul-gaussian-real.md): a special case with extra integrability hypotheses, which follows from this statement.
- [Posterior mean in the normal–normal model](../../bayesian-statistics/empirical-bayes-and-tweedie-s-formula/gaussian-posterior-mean-gaussian-real.md): applies this identity to the prior $\mathcal N(0, A)$.

## Sources

- I. M. Johnstone, *Gaussian Estimation: Sequence and Wavelet Models*, pre-publication draft of 16 September 2019, https://imjohnstone.su.domains/GE_09_16_19.pdf. Numbers refer to that draft.
- C. M. Stein, "Estimation of the mean of a multivariate normal distribution", *Ann. Statist.* 9 (1981) 1135–1151 (cited for attribution; not consulted for numbering).

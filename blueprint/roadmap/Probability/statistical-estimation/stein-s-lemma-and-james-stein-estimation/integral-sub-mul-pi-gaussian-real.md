# Stein's lemma, coordinate form

Let $X \sim \mathcal N_p(\theta, I)$, fix a coordinate $i$, and let $h : \mathbb R^p \to \mathbb R$ be such that, for almost every base point, its restriction to the line parallel to the $i$-th axis is differentiable everywhere, with partial derivative $\partial_i h$ integrable. If $(X_i - \theta_i)\, h(X)$ is integrable, then

$$\mathbb E[(X_i - \theta_i)\, h(X)] = \mathbb E[\partial_i h(X)] .$$

This is Johnstone's draft, equation (2.58) (there for $\theta = 0$). Unlike the [one-dimensional case](integrable-and-integral-sub-mul-gaussian.md), integrability of $(X_i - \theta_i) h(X)$ must be assumed: $h(x) = \exp(x_1^2)$ has $\partial_0 h = 0$ but $x_0 h(x)$ is not integrable.

## Informally uses

- [Stein's lemma](integrable-and-integral-sub-mul-gaussian.md): applied on each line parallel to the $i$-th axis, then integrated over the other coordinates by Fubini's theorem.

## Sources

- I. M. Johnstone, *Gaussian Estimation: Sequence and Wavelet Models*, pre-publication draft of 16 September 2019, https://imjohnstone.su.domains/GE_09_16_19.pdf. Numbers refer to that draft.

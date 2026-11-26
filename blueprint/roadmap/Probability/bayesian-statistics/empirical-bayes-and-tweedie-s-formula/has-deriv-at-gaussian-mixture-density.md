# The marginal density of a Gaussian location mixture is differentiable

Let $g$ be a finite measure on $\mathbb R$ and $v > 0$. The [marginal density](gaussian-mixture-density.md) $f(x) = \int \varphi_v(x - \mu)\, g(d\mu)$ is differentiable at every $x$, with

$$f'(x) = \int \frac{\mu - x}{v}\, \varphi_v(x - \mu)\, g(d\mu) .$$

No smoothness, density or moment assumption on $g$ is needed. The proof differentiates under the integral sign: $\partial_x \varphi_v(x - \mu) = \frac{\mu - x}{v} \varphi_v(x - \mu)$, and the bound $|t|\, e^{-t^2/(2v)} \le v + 1$ dominates this derivative by a constant, which is integrable because $g$ is finite.

Johnstone (draft, Section 2.3, before equation (2.26)) notes the stronger fact that $f$ is analytic, from the exponential-family form of the Gaussian kernel.

## Sources

- Iain M. Johnstone, *Gaussian Estimation: Sequence and Wavelet Models*, pre-publication draft of 16 September 2019, https://imjohnstone.su.domains/GE_09_16_19.pdf. Numbers refer to that draft.

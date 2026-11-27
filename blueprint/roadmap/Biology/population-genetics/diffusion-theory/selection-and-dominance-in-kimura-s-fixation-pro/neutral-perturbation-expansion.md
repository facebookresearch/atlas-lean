# Second-order expansion of Kimura's fixation probability in σ

For the Wright–Fisher diffusion with genic selection and scaled selection coefficient $\sigma$, Kimura's fixation probability from frequency $x$ is $u_\sigma(x) = (1 - e^{-2\sigma x})/(1 - e^{-2\sigma})$ for $\sigma \ne 0$ and $u_0(x) = x$; with $\sigma = 2Ns$ this is Kimura's diffusion formula $(1 - e^{-4Nsx})/(1 - e^{-4Ns})$ for genic selection (Kimura 1962, equation (8)). Kimura (1962, equation (9)) expands it in powers of $2Ns$ for $|2Ns| < \pi$ with Bernoulli-polynomial coefficients; its first three terms give

$$u_\sigma(x) = x + \sigma\,x(1 - x) + \frac{\sigma^2}{3}\,x(1 - x)(1 - 2x) + O(\sigma^3)$$

uniformly in $x \in [0, 1]$. Derivation: $1 - e^{-2\sigma x} = 2\sigma x\bigl(1 - \sigma x + \frac23\sigma^2x^2 + O(\sigma^3)\bigr)$ with the remainder uniform for $x \in [0, 1]$; dividing by the same series at $x = 1$ uses $(1 - \sigma + \frac23\sigma^2)^{-1} = 1 + \sigma + \frac13\sigma^2 + O(\sigma^3)$, and the product has $\sigma^2$-coefficient $\frac13 - x + \frac23x^2 = \frac13(1 - x)(1 - 2x)$. The first-order coefficient $x(1 - x)$ is the derivative in $\sigma$ at $\sigma = 0$. The second-order term is positive for $0 < x < 1/2$, zero at $x = 1/2$ and negative for $1/2 < x < 1$.

## Depends on

- [Kimura's fixation probability](../../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion/kimura-fixation.md)
- [Derivative of Kimura's fixation probability in σ at σ = 0](../../../../Biology/population-genetics/diffusion-theory/selection-and-dominance-in-kimura-s-fixation-pro/has-deriv-at-kimura-fixation-sigma-zero.md)
- [Kimura's fixation probability is continuous in σ at σ = 0](../../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion/continuous-at-kimura-fixation-zero.md)

## Expansion

1. The Taylor series of $1 - e^{-2\sigma x}$ in $\sigma$ with remainder bounds uniform in $x \in [0, 1]$.
2. The reciprocal of the denominator series for small $|\sigma|$, with an explicit range of validity.
3. The second-order coefficient and an explicit bound on the $O(\sigma^3)$ remainder.
4. Analyticity in $\sigma$: $u_\sigma(x)$ as a quotient of entire functions with a removable singularity at $\sigma = 0$; the nearest zeros of $1 - e^{-2\sigma}$ are at $\sigma = \pm i\pi$.

## Sources

- Original result: M. Kimura, On the probability of fixation of mutant genes in a population, Genetics 47 (1962), 713–719, equations (7)–(9). <https://doi.org/10.1093/genetics/47.6.713>

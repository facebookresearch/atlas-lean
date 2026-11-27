# Weil explicit formula for the zeta zero configuration

Let $k:\mathbb R\to\mathbb C$ be twice continuously differentiable with compact support and $h(z)=\int_{\mathbb R} k(u)e^{izu}\,du$. For a strip zero $\rho$, set $\gamma_\rho=(\rho-1/2)/i$ and let $m_\rho$ be its order of vanishing. The zero series below is absolutely convergent and includes both signs of the ordinate.
For $\psi=\Gamma'/\Gamma$ and the von Mangoldt function $\Lambda$,

$$
\sum_\rho m_\rho h(\gamma_\rho)=h(i/2)+h(-i/2)-\sum_{n\ge1}\frac{\Lambda(n)}{\sqrt n}\bigl(k(\log n)+k(-\log n)\bigr)+\frac{1}{2\pi}\int_{\mathbb R}h(r)\bigl(\operatorname{Re}\psi(1/4+ir/2)-\log\pi\bigr)\,dr.
$$

## Depends on

- [Zeros in a window](window-zeros.md)
- [The open critical strip](open-critical-strip.md)
- [Count with multiplicity](count-with-multiplicity.md)

## Proof depends on

- [Argument principle for a piecewise smooth Jordan contour](../../../../Analysis/complex-analysis/cauchy-theory/argument-principle/argument-principle-on-a-piecewise-smooth-jordan-contour.md)
- [Local zeta zero count](dyadic-riemann-von-mangoldt-and-local-count.md)

## Expansion

Move the weighted contour for the completed zeta logarithmic derivative, accounting for the two pole terms. Show summability of the zero series and identify the prime and gamma terms in the stated Fourier convention. Derive the bilinear form with the test $k=f*\widetilde g$, where $\widetilde g(u)=\overline{g(-u)}$. A truncated prime-counting Perron formula is not this identity.

## Sources

- Anthropic, [formalized argument](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/ExplicitFormula.lean#L53-L85).
- Anthropic, [formalized argument](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/WeilEF/Main.lean#L43-L57).
- Anthropic, [formalized argument](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/WeilEF/Main.lean#L263-L270).

# Weil explicit formula for a primitive Dirichlet character

Let $k:\mathbb R\to\mathbb C$ be twice continuously differentiable with compact support and $h(z)=\int_{\mathbb R} k(u)e^{izu}\,du$. For a strip zero $\rho$, set $\gamma_\rho=(\rho-1/2)/i$ and let $m_\rho$ be its order of vanishing. The zero series below is absolutely convergent and includes both signs of the ordinate.
Fix a primitive complex character $\chi$ of modulus $q>1$, of parity $\kappa\in\{0,1\}$ with $\chi(-1)=(-1)^\kappa$. For the zeros of $L(s,\chi)$ the formula is

$$
\sum_\rho m_\rho h(\gamma_\rho)=-\sum_{n\ge1}\frac{\Lambda(n)}{\sqrt n}\bigl(\chi(n)k(\log n)+\overline{\chi(n)}k(-\log n)\bigr)+\frac{1}{2\pi}\int_{\mathbb R}h(r)\bigl(\operatorname{Re}\psi(1/4+\kappa/2+ir/2)+\log(q/\pi)\bigr)\,dr,
$$

where $\Lambda$ is the von Mangoldt function and $\psi=\Gamma'/\Gamma$. In particular the negative-frequency prime term uses the conjugate coefficient, and no zeta pole term occurs.

## Depends on

- [Zeros in a window](../../riemann-zeta/zeros-of-the-riemann-zeta-function/window-zeros.md)
- [The open critical strip](../../riemann-zeta/zeros-of-the-riemann-zeta-function/open-critical-strip.md)
- [Count with multiplicity](../../riemann-zeta/zeros-of-the-riemann-zeta-function/count-with-multiplicity.md)

## Proof depends on

- [Argument principle for a piecewise smooth Jordan contour](../../../../Analysis/complex-analysis/cauchy-theory/argument-principle/argument-principle-on-a-piecewise-smooth-jordan-contour.md)
- [Local primitive L-function zero count](primitive-dirichlet-dyadic-zero-count.md)

## Expansion

Establish the full-line formula by moving the contour and applying the primitive functional equation, with the exact parity and conductor shifts. Specialize to correlation test functions to identify the zero-side and twisted prime-side Gram entries. A truncated Perron formula does not provide this bilinear equality.

## Sources

- Anthropic, [formalized argument](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/ThmE/EFLitChi.lean#L30-L49).
- Anthropic, [formalized argument](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/ThmE/MainChi.lean#L25-L47).

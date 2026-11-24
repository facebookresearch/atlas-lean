# Reflecting the frequency negates σ in the Wright–Fisher generator

For a real number $\sigma$, every real function $f$ and every real $y$, the
[backward generator](../wright-fisher-diffusion/generator.md) $L_\sigma$ of the Wright–Fisher
diffusion satisfies

$$(L_{-\sigma} f)(1 - y) = (L_\sigma g)(y), \qquad g(z) = f(1 - z).$$

Here $(L_\sigma u)(x) = \frac{x(1 - x)}{2}\, D(Du)(x) + \sigma\, x(1 - x)\, Du(x)$, where $D$ is the
derivative with the convention $Dh(x) = 0$ where $h$ is not differentiable at $x$, applied twice for
the second-order term; for twice-differentiable $u$ these are $u''$ and $u'$. No regularity of $f$
is needed: $Dg(y) = -Df(1 - y)$ and $D(Dg)(y) = D(Df)(1 - y)$ for every $y$, also where $f$ is not
differentiable. So the neutral part of the generator is invariant under $y \mapsto 1 - y$ and the
genic drift changes sign.

For twice continuously differentiable $f$ this is the identity that
[transports a solution to its reflection](one-sub.md).

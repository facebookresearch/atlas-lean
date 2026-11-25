# Without mutation the generator is the selection generator

For every real `α`, every real function `f` and every real `x`, the
[selection–mutation generator](selection-mutation-generator.md) with `θ₁ = θ₂ = 0` is the
[selection generator](../wright-fisher-diffusion/generator.md) with scaled selection coefficient
`α`: `(L_{α,0,0} f)(x) = x (1 - x) / 2 · D(Df)(x) + α x (1 - x) · Df(x)`, where, for a real function
`g`, `Dg(x)` is the derivative of `g` at `x` where it exists and `0` elsewhere.

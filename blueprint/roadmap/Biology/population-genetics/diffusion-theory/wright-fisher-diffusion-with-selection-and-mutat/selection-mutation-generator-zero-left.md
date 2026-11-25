# Without selection the generator is the mutation generator

For all real `θ₁`, `θ₂`, every real function `f` and every real `x`, the
[selection–mutation generator](selection-mutation-generator.md) with `α = 0` is the
[mutation generator](../wright-fisher-diffusion-with-mutation/mutation-generator.md):
`(L_{0,θ₁,θ₂} f)(x) = x (1 - x) / 2 · D(Df)(x) + (θ₁ (1 - x) - θ₂ x) / 2 · Df(x)`, where, for a real
function `g`, `Dg(x)` is the derivative of `g` at `x` where it exists and `0` elsewhere.

# The selection–mutation generator adds the two drifts

For all real `α`, `θ₁`, `θ₂`, every real function `f` and every real `x`, the [selection–mutation generator](selection-mutation-generator.md) is the
[selection generator](../wright-fisher-diffusion/generator.md) plus the [mutation generator](../wright-fisher-diffusion-with-mutation/mutation-generator.md) minus the neutral generator they share:

`(L_{α,θ₁,θ₂} f)(x) = (L_α f)(x) + (L^mut_{θ₁,θ₂} f)(x) - (L_0 f)(x)`.

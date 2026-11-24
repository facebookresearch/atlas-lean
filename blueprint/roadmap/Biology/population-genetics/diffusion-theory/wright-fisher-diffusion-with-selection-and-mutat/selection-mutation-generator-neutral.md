# The neutral generator applies the total derivative twice

For every real function `f` and every real `x`, the
[selection–mutation generator](selection-mutation-generator.md) with `α = θ₁ = θ₂ = 0` is
`(L_{0,0,0} f)(x) = x (1 - x) / 2 · D(Df)(x)`, where, for a real function `g`, `Dg(x)` is the
derivative of `g` at `x` where it exists and `0` elsewhere. Applying `D` twice is not the same as
setting an undefined classical second derivative to `0`: for `f(y) = (y - 1/2)² / 2` with `f(1/2)`
changed to `1`, `f` has no derivative at `1/2`, yet `Df(y) = y - 1/2` for every `y` and
`D(Df)(1/2) = 1`.

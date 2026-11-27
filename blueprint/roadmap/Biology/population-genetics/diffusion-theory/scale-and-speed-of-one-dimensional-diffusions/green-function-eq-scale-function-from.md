# The Green's function does not depend on the scale base point

Let `b`, `a` define a
[regular diffusion](../selection-duality-and-general-one-dimensional-di/is-regular-diffusion.md) on
`(0, 1)` (`a` positive and continuous on `(0, 1)`, `b / a` continuous on `(0, 1)` and integrable on
`[0, 1]`; accessibility of the endpoints and a probability normalization are not part of this), with
scale density `ψ`. For all `c, p, x ∈ [0, 1]`, the
[Dirichlet Green's function](../selection-duality-and-general-one-dimensional-di/green-function.md)
can be computed with the [scale function with base point](scale-function-from.md) `c`:

`G(p, x) = 2 A B / (C a(x) ψ(x))`, where `A = S_c(min(p, x)) - S_c(0)`,
`B = S_c(1) - S_c(max(p, x))` and `C = S_c(1) - S_c(0) = S(1) > 0`.

Division by `0` gives `0`, as in the definition of `G`: the denominator vanishes where `a(x) = 0`,
which the regularity hypotheses allow at `x = 0` and `x = 1`.

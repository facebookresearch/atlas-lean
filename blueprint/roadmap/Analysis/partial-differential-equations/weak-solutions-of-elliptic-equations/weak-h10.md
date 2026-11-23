# Weak H10

An element of `H¹₀(0,1)`, stored as its absolutely continuous
representative `toFun` on `[0,1]` together with a weak derivative
`weakDeriv ∈ L²(0,1)`.

In one dimension a function is in `H¹(0,1)` exactly when it has a continuous
representative that is a constant plus the primitive of an `L²(0,1)`
function, its weak derivative; it is in `H¹₀(0,1)` exactly when that
representative vanishes at both endpoints (Brezis, Chapter 8). The fields
encode this description:

- `toFun_eq_integral` makes `toFun` the primitive of `weakDeriv` on `[0,1]`,
  normalized by `toFun 0 = 0` (an empty integral). So `toFun` is absolutely
  continuous on `[0,1]`, vanishes at `0`, and `weakDeriv` plays the role of
  `u'`: it is the derivative of `toFun` at almost every point of `(0,1)`.
- `integral_weakDeriv_eq_zero` is the condition at the other endpoint: by
  `toFun_eq_integral` at `x = 1`, `toFun 1 = ∫₀¹ weakDeriv`, so the field
  says exactly `toFun 1 = 0`.

Values of `toFun` and `weakDeriv` outside `[0,1]` are unconstrained and do
not enter `weak_diffusion_exists_unique`, which reads `toFun` only on `[0,1]`
and `weakDeriv` only through integrals over `[0,1]`.

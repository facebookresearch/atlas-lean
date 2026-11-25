# Elements of H¹₀(0, 1) as primitives of square-integrable derivatives

An element of `H¹₀(0,1)` is given by two real functions `u` and `w` such that `w` is square
integrable on `[0,1]`, `u(x) = ∫₀ˣ w(t) dt` for every `x ∈ [0,1]`, and `∫₀¹ w(t) dt = 0`. The
function `u` is the absolutely continuous representative and `w` its weak derivative: `w` is the
derivative of `u` at almost every point of `(0,1)`. The formula for `u` at `x = 0` gives `u(0) = 0`
(an empty integral), and at `x = 1` it turns the condition `∫₀¹ w(t) dt = 0` into `u(1) = 0`.

In one dimension a function is in `H¹(0,1)` exactly when it has a continuous representative that
is a constant plus the primitive of an `L²(0,1)` function, its weak derivative; it is in
`H¹₀(0,1)` exactly when that representative vanishes at both endpoints (Brezis, Chapter 8). The
values of `u` and `w` outside `[0,1]` are unconstrained; the
[weak formulation of steady diffusion](weak-diffusion-exists-unique.md) uses `u` only on `[0,1]`
and `w` only through integrals over `[0,1]`.

# Turing pattern branch from the Lyapunov–Schmidt reduction

Let mode `i₀`, with
wavenumber `k = κ i₀`, be admissible (`0 < f_u k² - d_u k⁴`) with neutral diffusion
`d₀ = d_n(k²)`, negative trace there, `f_v ≠ 0`, and no other mode critical at `d₀`. Let
`F(w, d)` be a map on Neumann-mode coefficients with the trivial branch `F(0, d) = 0`, strictly
differentiable at `(0, d₀)`, whose linearization along the trivial branch is the Turing
linearization `D(d) ∂ₓₓ + J` (`modeOperator J du d κ`) for every `d` near `d₀`. Fix a Fredholm
package of the linearization at `d₀`, and let `G` be a factor, strictly differentiable at
`(0, d₀)`, of the scalar bifurcation function for the critical mode and the normalized critical
functional: `G̃(a, d) = a G(a, d)` near `(0, d₀)`. Then

* `∂_d G(0, d₀)` is the crossing speed `(d_u k⁴ - f_u k²) / tr (J - k² D(d₀))` of the critical
  eigenvalue (`leadingEigenvalue_crossing`), in particular positive;
* near `d₀`, `G(0, d)` has the sign of the critical eigenvalue
  `leadingEigenvalue (J - k² D(d))`;
* there is a branch `d = β(a)` with `β 0 = d₀` and slope `-∂_a G / ∂_d G` at `0` such that near
  `(0, d₀)` the zeros of `F` are exactly the trivial ones `w = 0` and the branch
  `w = a φ + W(a φ, d)`, `d = β(a)`;
* for small `a ≠ 0` the branch state `a φ + W(a φ, β(a))` is a **nonzero** steady state at
  `d = β(a)` (a pattern);
* `G(0, d)` is negative for `d < d₀` and positive for `d > d₀` near `d₀`.

The trivial-branch values `G(0, d)` are not assumed; they are derived from the reduction
(`lsScalar_factor_normalization`), and they agree with the critical eigenvalue only to first
order at `d₀`.

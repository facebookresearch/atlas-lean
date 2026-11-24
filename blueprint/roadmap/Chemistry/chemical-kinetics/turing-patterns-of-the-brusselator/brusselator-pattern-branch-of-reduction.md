# Turing pattern branch of the Brusselator

Let `a ≠ 0` and `b < 1 + a²` (the steady state
`(a, b / a)` is stable without diffusion), `d_u ≥ 0`, and let mode `i₀`, with wavenumber
`k = κ i₀`, be admissible, `0 < (b - 1) k² - d_u k⁴`, with neutral inhibitor diffusion
`d₀ = a² (1 + d_u k²) / ((b - 1) k² - d_u k⁴)`, and no other mode critical at `d₀`. Let `F(w, d)`
be a map on Neumann-mode coefficients with the trivial branch `F(0, d) = 0`, strictly
differentiable at `(0, d₀)`, whose linearization along the trivial branch is the Brusselator
linearization `D(d) ∂ₓₓ + J` for every `d` near `d₀`, and let `G` be a factor, strictly
differentiable at `(0, d₀)`, of the scalar bifurcation function for the critical mode and the
normalized critical functional. Then

* `∂_d G(0, d₀) = (d_u k⁴ - (b - 1) k²) / (b - 1 - a² - k² (d_u + d₀))`, and it is positive;
* near `d₀`, `G(0, d)` has the sign of the critical eigenvalue of `J - k² D(d)`;
* there is a branch `d = β(s)` through `β 0 = d₀` such that near `(0, d₀)` the zeros of `F` are
  exactly the trivial ones and the branch `w = s φ + W(s φ, d)`, `d = β(s)`;
* for small `s ≠ 0` the branch state is a **nonzero** steady state at `d = β(s)` (a pattern);
* `G(0, d)` is negative for `d < d₀` and positive for `d > d₀` near `d₀`.

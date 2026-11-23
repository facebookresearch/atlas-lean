# Weak stationarity against the speed measure (boundary-flux form)

For a regular
diffusion with drift `b` and variance `a`, the integral of `L f` against the speed measure
`m` is the net boundary flux of `f' / ψ`: `∫ L f ∂m = L1 - L0`, where `L0` (resp. `L1`) is
the one-sided limit of `f' / ψ` at `0` from the right (resp. at `1` from the left). The
identity is the integrated canonical form `L f = (1 / m) (f' / ψ)'`
(`diffusionGenerator_eq_one_div_speedDensity`): against `m`, the integrand is the derivative
`(f' / ψ)'`, so only the endpoint flux values survive. `IsRegularDiffusion` gives positivity
of `a` and `ψ` on `(0, 1)`; `ContDiffOn 2` makes `L f` continuous there with `deriv`
agreeing with the one-sided derivatives; the flux limits supply the boundary values; and
integrability makes the integral a genuine value. This is analytic stationarity only: no
invariance of any process law, no reversibility or Dirichlet-form identity, and no claim
that the speed measure is finite.

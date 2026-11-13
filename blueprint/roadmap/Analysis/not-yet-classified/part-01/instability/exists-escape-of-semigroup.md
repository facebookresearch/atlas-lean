# Linearized instability for a semilinear flow from its linearized semigroup

`S` is the linearized semigroup at the equilibrium `u₀` (for a semilinear parabolic problem,
`S t = e^{t B}` with `B` the linearization; Henry 1981, §5.1), with growth bound
`‖S t‖ ≤ M e^{ω t}`. The eigenvalue enters only through `hSφ : S T φ = e^{T κ} φ` at the
chosen time `T > 0`, with `Re κ > 0`. The theorem does not relate `κ` to a generator: `hSφ` is
the spectral-mapping input (an eigenvalue `κ` of the generator `B` with eigenvector `φ` gives
`e^{T B} φ = e^{T κ} φ`), to be supplied by the semigroup construction. The time-`T` map of
the flow is `u₀ + S T y + O(‖y‖ᵖ)` near `u₀`. If `ω < p · Re κ` (in particular, if `κ` is a dominant
eigenvalue and `S` has growth bound `Re κ`), then `u₀` is unstable.

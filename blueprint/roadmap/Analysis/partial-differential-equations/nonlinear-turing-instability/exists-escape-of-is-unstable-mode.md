# Nonlinear instability from an unstable Neumann mode, time-map form

Let `J` be the Jacobian of the kinetics at a homogeneous steady state `u₀` with `tr J < 0`,
`d_u, d_v ≥ 0`, and let the Neumann mode `n` on `[0, L]` be linearly unstable
(`IsUnstableMode J d_u d_v k_n`, e.g. from `isUnstableMode_neumannWavenumber_iff`). The phase
space is `C([0, L]; ℝ²)` with the sup norm. Assume:

* **semigroup**: the linearized semigroup `S` is a C₀ semigroup acting on the Neumann mode `n`
  through the modal ODE of `J - k_n² D` (`ActsByModalODE`), with growth bound
  `‖S t‖ ≤ M e^{ω t}` where `ω < p λ` for the growth rate `λ = growthRate J d_u d_v k_n`
  (e.g. `ω = λ + ε` when the mode `n` is dominant);
* **differentiability**: the time-`T` map of the nonlinear flow `Φ` is
  `u₀ + S T y + O(‖y‖ᵖ)` on the ball `‖y‖ ≤ ρ` (derived from a Hölder-differentiable reaction in
  `exists_norm_timeMap_sub_le`);
* **flow**: `Φ` starts at the identity and steps by its time-`T` map along orbits that stay in
  the ball.

Then `u₀` is nonlinearly unstable: some distance `ε > 0` is reached at a nonnegative time from
initial data arbitrarily close to `u₀`.

Stability without diffusion (`0 < det J`) is not assumed, so this is not by itself a Turing
instability: it also applies when the kinetics alone are unstable. The diffusion-driven case is
`turing_instability_exists_escape`.

# Nonlinear instability from an unstable Neumann mode (mild formulation)

The two-species system `u_t = D u_xx + f(u)` on `[0, L]` with Neumann boundary conditions, in
the phase space `C([0, L]; ℝ²)` (sup norm) of PDE-01, at a homogeneous steady state `a`
(`f a = 0`). Hypotheses:

* **spectral input** (from `TuringPatterns`): `tr J < 0`, `d_u, d_v ≥ 0`, and the Neumann
  mode `n` is linearly unstable, `IsUnstableMode J d_u d_v k_n` (stability without diffusion,
  `0 < det J`, is not assumed; see `turing_instability_exists_escape_of_mild` for the Turing
  case);
* **differentiability**: the kinetics are Lipschitz on bounded sets and have Jacobian `J` at `a`
  with a Hölder remainder `‖f (a + z) - f a - J z‖ ≤ K ‖z‖ᵖ` (`‖z‖ ≤ r`, `p > 1`; e.g. `f` of
  class `C²` with `p = 2`);
* **semigroups**: the diffusion semigroup `SA` (`e^{t D Δ_N}`) is C₀ and fixes the constant
  state; the linearized semigroup `S` is C₀, its orbits are the mild solutions of
  `w' = D Δ_N w + J w`, it acts on the Neumann mode `n` through the modal ODE of
  `J - k_n² D`, and it has growth bound `‖S t‖ ≤ M e^{ω t}` with `ω < p λ`, where
  `λ = growthRate J d_u d_v k_n`;
* **flow**: `Φ` starts at the identity, steps by its time-`T` map along orbits in the ball
  `‖x - a‖ ≤ ρ₀`, and from that ball gives mild solutions on `[0, T]` bounded by `R`
  (the local-flow instantiation of PDE-01 for the Turing system supplies these).

Then the steady state is nonlinearly unstable.

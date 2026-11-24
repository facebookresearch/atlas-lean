# Nonlinear Turing instability, time-map form

The diffusion-driven case of `exists_escape_of_isUnstableMode`: the kinetics are stable without
diffusion (`tr J < 0`, `0 < det J`, Turing's first condition), and the Neumann mode `n` on
`[0, L]` is linearly unstable for the reaction–diffusion system (`d_u, d_v ≥ 0`). Besides the
semigroup, differentiability and flow hypotheses of `exists_escape_of_isUnstableMode`, the
linearized semigroup `S` acts on the homogeneous mode (the constant states, `k_0 = 0`) through the
kinetics ODE `c' = J c` (`ActsByModalODE S 0 J`); this ties the stability of `J` to `S`.

Conclusions: homogeneous perturbations stay bounded under `S`
(`‖S t (const w)‖ ≤ C ‖w‖`), the homogeneous mode is not linearly unstable, the unstable mode is
non-homogeneous (`0 < n`), and the homogeneous steady state `u₀` is nonlinearly unstable: some
distance `ε > 0` is reached at a nonnegative time from initial data arbitrarily close to
`u₀`.

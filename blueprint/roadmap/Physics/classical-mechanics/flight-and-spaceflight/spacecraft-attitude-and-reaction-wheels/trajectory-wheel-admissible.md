# A feasible trajectory for the reduced wheel plant

Let `I > 0`, `k > 0` and `U_max`, `ω₀`, `h₀`, `h_max` be real numbers with `|ω₀| ≤ U_max / k`
and `|h₀| + I |ω₀| ≤ h_max`. Then on every horizon `[0, T]` with `T ≥ 0`, the
[wheel command](wheel-command.md) `t ↦ u_w(ω(t))` along the
[rate trajectory](rate-trajectory.md) `ω(t) = ω₀ exp(−k t / I)` and the
[wheel momentum](wheel-momentum.md) `h_w(t) = h₀ + I ω₀ (1 − exp(−k t / I))` are
[admissible](wheel-admissible.md) for the command limit `U_max` and the momentum limit `h_max`:
`|u_w(ω(t))| ≤ U_max` and `|h_w(t)| ≤ h_max` for every `t ∈ [0, T]`. The reserve does not grow
with the horizon.

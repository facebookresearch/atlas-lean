# Stagnation temperature and pressure across a normal shock

Let `γ > 1` and `R > 0`, and let an upstream state `(ρ1, u1, p1, T1)` and a downstream state
`(ρ2, u2, p2, T2)` with `ρ1, T1, ρ2, T2 > 0` satisfy the
[normal-shock jump conditions](is-normal-shock-jump.md). Let each stagnation state be fixed by the
stagnation energy balance `cp T_i + u_i² / 2 = cp T0_i` with `cp = γ R / (γ - 1)`, a stagnation
density `ρ0_i > 0`, the ideal-gas law `p0_i = ρ0_i R T0_i` and the isentropic connection
`p_i / ρ_i^γ = p0_i / ρ0_i^γ` (`i = 1, 2`). Then the stagnation temperatures agree, `T02 = T01`, and
`p02 / p01 = exp(-Δs / R)`, with the [specific entropy change](specific-entropy-change.md)
`Δs = cv log (T2 / T1) + R log (v2 / v1)` with `cv = R / (γ - 1)` and the specific volumes
`v_i = 1 / ρ_i`, on either branch.

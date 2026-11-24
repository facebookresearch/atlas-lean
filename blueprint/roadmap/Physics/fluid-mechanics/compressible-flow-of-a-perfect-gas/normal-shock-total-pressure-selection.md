# Total pressure across the two normal-shock branches

Let `γ > 1` and `R > 0`, and let an upstream state `(ρ1, u1, p1, T1)` and a downstream state
`(ρ2, u2, p2, T2)` with `ρ1, T1, ρ2, T2 > 0` satisfy the
[normal-shock jump conditions](is-normal-shock-jump.md). Let `a1² = γ R T1` and `M1 = |u1| / a1`.
Suppose the downstream state is not the upstream one. Let `M1 > 0`. Let each stagnation state be
fixed by the stagnation energy balance `cp T_i + u_i² / 2 = cp T0_i` with `cp = γ R / (γ - 1)`, a
stagnation density `ρ0_i > 0`, the ideal-gas law `p0_i = ρ0_i R T0_i` and the isentropic connection
`p_i / ρ_i^γ = p0_i / ρ0_i^γ` (`i = 1, 2`). Then for `M1 > 1` the total pressure falls, `p02 < p01`.
For `M1 < 1` the solution is on the expansion branch `(γ - 1) / (2 γ) < M1² < 1`, where the total
pressure rises, `p01 < p02`, and the [specific entropy change](specific-entropy-change.md)
`Δs = cv log (T2 / T1) + R log (v2 / v1)` with `cv = R / (γ - 1)` and the specific volumes
`v_i = 1 / ρ_i` is negative: the expansion root is entropy-inadmissible.

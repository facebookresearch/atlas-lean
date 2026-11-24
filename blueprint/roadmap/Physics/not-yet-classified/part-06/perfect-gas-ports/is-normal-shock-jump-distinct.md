# Is Normal Shock Jump distinct

The distinct branch solves the jump conditions: for `γ > 1`, `R > 0`, an upstream perfect-gas
state `p1 = ρ1 R T1` with `T1 > 0` and `u1 > 0`, sound speed `a1 ^ 2 = γ R T1` and Mach number
`M1 = |u1| / a1`, the state with `ρ2 = ρ1 r`, `u2 = u1 / r`, `p2 = p1 P` and `T2 = T1 P / r`,
where `r` and `P` are the density and pressure ratios at `m = M1 ^ 2`, satisfies the jump
conditions. This holds whatever the sign of `P`: it is an algebraic statement, and
`isNormalShockJump_distinct_pos_iff` says when the root is a positive state.

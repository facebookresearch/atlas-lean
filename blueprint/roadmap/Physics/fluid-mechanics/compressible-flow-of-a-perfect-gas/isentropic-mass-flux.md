# Isentropic mass flux per unit area of a perfect gas

For a stagnation pressure `p0`, a stagnation temperature `T0`, a specific gas constant `R`, a
heat-capacity ratio `γ` and a Mach number `M` (real numbers), the isentropic mass flux per unit area
is `G(M) = p0 √(γ / (R T0)) M (1 + (γ - 1) M² / 2)^(-(γ + 1) / (2 (γ - 1)))`, with a real power. It
is defined for all real inputs, with the conventions `√x = 0` for `x < 0`, `x / 0 = 0` (so the
square-root factor is `0` when `R T0 = 0`, and the exponent is `0` when `γ = 1`), and
`s^t = |s|^t cos(π t)` for a negative base `s`, which occurs only for `γ < 1`. The physical domain
is `p0, T0, R > 0`, `γ > 1` and `M ≥ 0`.

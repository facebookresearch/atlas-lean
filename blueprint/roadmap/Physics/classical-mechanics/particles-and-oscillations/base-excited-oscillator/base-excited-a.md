# State matrix of the base-excited oscillator

For real numbers `m`, `c` and `k`, the state matrix of the base-excited oscillator is the `2 × 2`
real matrix

`A = [[0, 1], [-(k / m), -(c / m)]]`,

acting on the state `(u, u')`, the displacement of the mass relative to the base and its velocity:
row `0` encodes `u' = v` and row `1` the relative equation `m u'' + c u' + k u = p - m a_g` divided
by `m`. On `ℝ × ℝ` it is the [phase-space operator](../forced-damped-oscillator-and-resonance/phase-operator.md)
`(x, v) ↦ (v, -(k x + c v) / m)` of the mass–spring–damper. In the physical reading `m > 0`,
`c ≥ 0` and `k > 0`; the matrix is defined for all real inputs, and with the convention `u / 0 = 0`
its second row is `[0, 0]` when `m = 0`.

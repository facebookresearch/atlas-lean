# Single-pulse response

Let `(vr, wr)` be a rest state, let a solution start at the
post-pulse state `(vr + δ, wr)`, and let `T ≥ 0`. Suppose `|v + a - b w| ≤ M` on `[0, T]` (for
`b, ε > 0` such an
`M` comes from the trapping ellipse, `abs_le_of_energy_le`), and put `η = |ε| M T`.

* If the post-pulse drift is negative with margin `η`, i.e. `δ (1 - vr² - vr δ - δ²/3) + η < 0`,
  the voltage never exceeds its post-pulse value `vr + δ` on `[0, T]`.
* If the voltage field at the frozen recovery value satisfies `vField I u wr ≥ m > η` on
  `[vr + δ, γ]` (in particular the voltage rises after the pulse, with margin `η`) and
  `γ - (vr + δ) ≤ (m - η) T`, the voltage reaches `γ` within `[0, T]`.

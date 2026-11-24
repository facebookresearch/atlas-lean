# Min Drag Speed

Minimum-drag speed `V_md = √(√(b / a))`. For positive weight and `ρ, S, CD0, k > 0` it is the
unique positive speed of least level-flight drag
(`levelDrag_eq_two_sqrt_iff_eq_minDragSpeed`). As a formula it is the positive root of
`V ^ 4 = b / a` whenever `W ≠ 0` and `ρ, S, CD0, k > 0` (`minDragSpeed_pos`,
`minDragSpeed_pow_four`). If `CD0 = 0`, `k = 0` or `W = 0`, Lean's conventions `x / 0 = 0` and
`√0 = 0` give the value `0`, which is not a positive speed: with `ρ, S > 0` and `CD0, k ≥ 0` the
drag then has no minimum over positive speeds when exactly one of its two terms vanishes, and
every positive speed is a minimizer when both vanish.

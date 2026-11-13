# Student's `t` law

**Student's `t` law** with `k` degrees of freedom (Casella–Berger, Definition 5.3.4): the
measure with Lebesgue density `Γ((k + 1)/2) / (√(k π) Γ(k/2)) · (1 + t²/k)^{-(k+1)/2}`.
It is the law of `Z / √(V / k)` for independent `Z ~ N(0, 1)`, `V ~ χ²_k`
(`map_div_sqrt_chiSquare_eq_studentT`). It is a probability measure for `k ≥ 1`
(`isProbabilityMeasure_studentTMeasure`); for `k = 0` it is the zero measure.

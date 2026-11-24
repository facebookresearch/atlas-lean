# Arzelà–Ascoli in `C((0,1))`

A uniformly bounded equicontinuous family of continuous
paths on `[0,1]` has compact closure (Billingsley 1999, Theorem 7.2). The proof transports
Mathlib's `BoundedContinuousFunction.arzela_ascoli` along the isometry
`C([0,1]) ≃ᵢ [0,1] →ᵇ ℝ`. Moved from the private copies
`donsker_isCompact_closure_of_bounded_equicontinuous` in `MathlibExt.Probability.Donsker` and
`isCompact_closure_of_bounded_equicontinuous'` in
`MathlibExt.Probability.Martingale.MartingaleTightness`.

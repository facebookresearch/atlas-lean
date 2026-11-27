# Forward solutions of the competition equations

`z` solves the competition equations at
every time `t ≥ 0`: `z'(t) = field (z t)`. The derivative is two-sided (`HasDerivAt`) at `t = 0`
too, so a trajectory given only on `[0, ∞)` must be extended to negative times with that
derivative at `0`; one that is only right-differentiable at `0` does not qualify. A solution on an
open interval containing `[0, ∞)` qualifies, and negative times matter only through the
derivative at `0`. Equivalently, `t ↦ ![(z t).1, (z t).2]` solves the Lotka–Volterra system
`IsLVSolution` (`isSolution_iff_isLVSolution`).

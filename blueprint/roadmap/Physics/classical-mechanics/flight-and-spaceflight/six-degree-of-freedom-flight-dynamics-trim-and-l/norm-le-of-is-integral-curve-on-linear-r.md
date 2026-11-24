# Exponential decay, by the direct method

Every forward solution of the reduced linear
plant on `[0, ∞)` satisfies `‖e t‖ ≤ √8 * exp (-t / 4) * ‖e 0‖` for `t ≥ 0`: along it `V` has
derivative `-‖e‖² ≤ -V / 2`, so `V` decays at least as `exp (-t / 2)`, and the comparison bounds
give the factor `√(2 / (1/4)) = √8`. From the trim, `e 0 = 0`, the bound forces `e t = 0`: no
decay is claimed there.

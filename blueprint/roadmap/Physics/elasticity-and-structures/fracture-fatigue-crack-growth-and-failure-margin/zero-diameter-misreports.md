# Zero diameter misreports

The zero diameter is rejected, not covered: at `d = 0` Lean's `x / 0 = 0` makes both stress
formulas vanish, so every calibrated functional reports zero demand and no failure for every
load. The hypothesis `0 < d` of the sizing results cannot be dropped.

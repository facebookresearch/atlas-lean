# Optimal savings under log utility

A young worker with wage `w > 0`,
discount factor `β > 0`, and gross return `R = 1 + r > 0` on savings chooses
`s` in `(0, w)` to maximize `log (w - s) + β * log (R * s)` (log consumption
when young plus discounted log consumption when old). The maximum is attained
at `s = olgSavings β w = β / (1 + β) * w`, independent of `R`. The proof uses
the weighted log inequality from `Real.log_le_sub_one_of_pos`: the weighted
average of the ratios `(w - s) / (w - s*)` and `s / s*` with weights
`1 / (1 + β)` and `β / (1 + β)` equals `1`; no calculus is used.

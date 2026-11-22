# Step

C6: deterministic backlogging transition on `(net stock, length-L pipeline)`
with order `q` and demand `d` inputs. The receipt is the pipeline head for
`L > 0` and the immediate order `q` for `L = 0`. New stock adds the receipt
and subtracts demand in `ℝ` (no cap, no saturation). The new pipeline is the
old tail followed by `q` (vacuous at `L = 0`). Deterministic by construction;
MDP-ready interface only, not a finite-state MDP instance.

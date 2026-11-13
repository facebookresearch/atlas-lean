# Profile log-odds score of a residue

The profile log-odds score `log (p a / q a)` of residue `a`: `p` is the position-specific
profile probability (estimated from aligned homologs), `q` the background probability.
Meaningful for `p a, q a > 0`; otherwise Lean's `log 0 = 0` and `x / 0 = 0` give junk.

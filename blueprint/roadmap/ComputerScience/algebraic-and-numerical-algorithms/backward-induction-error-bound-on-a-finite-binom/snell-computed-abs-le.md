# Snell computed abs le

Let `0 ≤ p ≤ 1`, `disc > 0` and `ε ≥ 0`. Any computed recursion `V` with exact terminal values (`V 0 = g`) whose every update deviates by at most `ε` from the exact Snell update `max (g s) (disc · (p V(true :: s) + (1 - p) V(false :: s)))` stays within `ε ∑_{j < N} disc^j` of the Snell envelope `snell p disc g` after `N` steps, at every node and in particular at the root.

# Backward-induction value of a path-dependent claim

For real `u`, `d`, `R` and a claim `V` that assigns a real payoff `V(s)` to every finite history
`s` of up and down moves, the backward-induction value with `k` periods left at history `s` is
`v_0(s) = V(s)` and `v_{k+1}(s) = (q * v_k(s, up) + (1 - q) * v_k(s, down)) / R`, the discounted
risk-neutral average of the values at the two successor nodes. Here `(s, up)` and `(s, down)`
extend `s` by one up or one down move, and `q = (R - d) / (u - d)` is the risk-neutral up
probability. Division follows the convention x / 0 = 0: `q = 0` when `u = d`, and
`v_{k+1}(s) = 0` when `R = 0`.

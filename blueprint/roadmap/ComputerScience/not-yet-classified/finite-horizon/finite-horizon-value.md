# Finite Horizon Value

Finite-horizon value: `k` steps of value iteration from the zero terminal
value. With `0` steps remaining the value is `0` (no terminal reward); with
`k + 1` steps remaining it is one Bellman optimality update of the `k`-step
value (`finiteHorizonValue_succ`).

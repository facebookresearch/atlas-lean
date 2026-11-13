# Confounded Net

The confounded network `Z → X`, `Z → Y`, `X → Y` on `Bool` (nodes `Z = 0`, `X = 1`,
`Y = 2`, each node's parents are all earlier nodes): `Z` is a fair coin; `X` is `true` with
probability `4/5` if `Z` and `1/5` otherwise; `Y` is `true` with probability `9/10`, `1/2`,
`1/2`, `1/10` for `(X, Z) = (true, true), (true, false), (false, true), (false, false)`.

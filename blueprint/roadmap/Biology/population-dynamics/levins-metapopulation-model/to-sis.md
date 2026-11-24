# A Levins solution gives an SIS solution with S = 1 − p and N = 1

For all real numbers `c` and `e`, if `p` is a [solution](is-solution-2.md) of the Levins equation
`p' = c p (1 - p) - e p`, then `S = 1 - p` and `I = p` form a
[solution of the closed-population SIS system](../../epidemiology/sis-epidemic-model/is-solution.md)
with transmission rate `β = c`, recovery rate `γ = e` and population size `N = 1`:
`S' = -c S I + e I` and `I' = c S I - e I` at every `t ≥ 0`.

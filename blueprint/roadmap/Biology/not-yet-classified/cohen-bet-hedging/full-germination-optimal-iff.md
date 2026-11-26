# Germination optimality criterion

**Germination optimality criterion** (derived from Cohen's 1966 seed-bank model): let `μ` be a
probability measure, `0 < s < 1`, and `Y` a measurable yield with `Y > 0` everywhere such that
`log Y` and `1 / Y` are integrable. Then full germination maximizes the long-run growth rate, i.e.
`ρ(H) ≤ ρ(1)` for every `H ∈ [0, 1]`, if and only if `s E[1/Y] ≤ 1`. Equivalently, some
germination fraction `H < 1` does strictly better than `H = 1` if and only if `s E[1/Y] > 1`.
This exact criterion is derived directly from the left derivative `1 - s E[1/Y]` of the concave
function `ρ(H) = E[log(H Y + (1 - H) s)]` at `H = 1` in Cohen's seed-bank model.

## Sources

- Model provenance — D. Cohen, "Optimizing reproduction in a randomly varying environment", J. Theor. Biol. 12 (1966) 119–129, doi:10.1016/0022-5193(66)90188-3; criterion derived from the left derivative at `H = 1`.

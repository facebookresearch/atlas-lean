# Certified lower bound on the dispatch cost

For rational `d`, `p_min`, `p_max`, `f_min`, `f_max`, prices `λ` and bound multipliers `μ_hi`,
`μ_lo`, `η_hi`, `η_lo`, the certified lower bound is

`L = d · λ + p_min · μ_lo - p_max · μ_hi + f_min · η_lo - f_max · η_hi`.

For a [dual feasible](is-dual-feasible.md) witness accepted by the checker it bounds the cost of
every feasible dispatch from below ([correctness](dispatch-certificate-correct.md)).

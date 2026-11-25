# Expected shortfall via the Rockafellar–Uryasev formula

For a loss `X` on a finite sample space with weights `p(ω)` and a level `α` (in use, `0 < α < 1`),
the expected shortfall is given by the Rockafellar–Uryasev formula
`ES_α(X) = inf_c (c + E[(X - c)⁺] / (1 - α))`, the infimum over all real `c`, where
`E[(X - c)⁺] = ∑_ω p(ω) max(X(ω) - c, 0)`. For probability weights, `p(ω) ≥ 0` with `∑_ω p(ω) = 1`,
and `0 < α < 1`, this is the expected shortfall of `X` under `p`, and the objective is convex in
`c`. The formula is evaluated for all real weights, with the raw weights (nothing is clamped, unlike
the [quantile form](quantile-expected-shortfall.md)). The infimum is taken in the real numbers, so
it is `0` when these values are not bounded below; this happens for `α = 1`, where the convention
`x / 0 = 0` reduces the objective to `c`.

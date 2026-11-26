# Rockafellar–Uryasev infimum is attained at value at risk

For a loss `X` on a finite sample space with weights `p(ω) ≥ 0` summing to `1` and a level
`0 < α < 1`, the infimum over real `c` of `c + E[(X - c)⁺] / (1 - α)`, with
`E[(X - c)⁺] = ∑_ω p(ω) max(X(ω) - c, 0)`, is attained at the value at risk
`VaR_α(X) = q_X(α)`, the lower `α`-quantile `q_X(α) = inf {x : P(X ≤ x) ≥ α}` of the loss,
where `P(X ≤ x) = ∑_{ω : X(ω) ≤ x} p(ω)`: `ES_α(X) = q_X(α) + E[(X - q_X(α))⁺] / (1 - α)`.

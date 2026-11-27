# Quantile and Rockafellar–Uryasev expected shortfalls agree

For a loss `X` on a finite sample space with weights `p(ω) ≥ 0` summing to `1` and a level
`0 < α < 1`, the quantile-integral and Rockafellar–Uryasev definitions of expected shortfall
agree: `(1 - α)⁻¹ ∫_α^1 q_X(u) du = inf_c (c + E[(X - c)⁺] / (1 - α))`, where
`q_X(u) = inf {x : P(X ≤ x) ≥ u}`, with `P(X ≤ x) = ∑_{ω : X(ω) ≤ x} p(ω)`, is the lower
quantile of the loss and `E[(X - c)⁺] = ∑_ω p(ω) max(X(ω) - c, 0)`.

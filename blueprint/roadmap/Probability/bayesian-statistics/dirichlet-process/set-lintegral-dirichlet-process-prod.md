# Ferguson's conjugacy

**Ferguson's conjugacy** (Ferguson 1973, Theorem 1): given `n` observations `xs` from
`G ∼ DP(α, H)`, the posterior of `G` is `DP(α + n, (α H + ∑ᵢ δ_{xsᵢ}) / (α + n))`. Stated as
the disintegration `P(G ∈ S, X₀ ∈ A₀, …) = ∫_{∏ Aᵢ} DP(α + n, posterior base)(S) dP(xs)` over
the urn law of the observations.

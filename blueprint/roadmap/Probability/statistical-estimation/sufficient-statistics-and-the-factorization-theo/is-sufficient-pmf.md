# Sufficient statistic for a discrete family

A statistic `T : X → τ` is *sufficient* for the discrete family `P : Θ → PMF X` if the
conditional probability `P θ x / P_θ(T = T x)` of `x` given `T = T x` is the same under any
two parameters `θ, θ'` for which `{T = T x}` has positive probability. Here
`P_θ(T = t) = (P θ).map T t`.

# Real-valued log-MGF expression

**Real-valued log-MGF expression** `Λ(t) = log E[exp ⟪t, X⟫]`.

For a random vector `X : Ω → ℝᵈ`, this returns the logarithm of the moment
generating function evaluated at the dual variable `t ∈ ℝᵈ`, using the Euclidean
inner product. Under a probability measure it represents the cumulant generating
function at directions where the exponential is integrable. For a nonintegrable
exponential, the Bochner integral is `0` and `Real.log 0 = 0`, so this definition
returns `0`. The bounds below explicitly require exponential integrability.
Ported from v1.

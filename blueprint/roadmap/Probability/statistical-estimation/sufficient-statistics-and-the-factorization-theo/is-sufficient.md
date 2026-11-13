# Sufficient sub-σ-algebra

A sub-σ-algebra `m` is *sufficient* for the family of measures `P` on `(Ω, m₀)` if
`m ≤ m₀`, every `P θ` is finite, and for every `m₀`-measurable set `s` one `m`-measurable
function is a version of the conditional probability `P_θ[1_s | m]` under every `P θ`.
Bundling `m ≤ m₀` and finiteness into the predicate means an `IsSufficient` hypothesis
itself represents a sufficient sub-σ-algebra for statistical laws: the conditional
expectations it mentions are genuine, not Mathlib's totalized fallback on unrelated
σ-algebras or infinite measures.

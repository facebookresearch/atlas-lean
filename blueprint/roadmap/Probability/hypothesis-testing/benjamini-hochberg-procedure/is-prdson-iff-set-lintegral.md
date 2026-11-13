# PRDS as a monotone version of a conditional probability

For measurable p-values,
`IsPRDSOn μ p H0` holds iff for every `i ∈ H0` and measurable increasing `D` there is a
nondecreasing `g` with `μ (P ∈ D, p i ∈ B) = ∫⁻ x in B, g x ∂(law of p i)` for every Borel `B`,
i.e. `g` is a nondecreasing version of `x ↦ P(P ∈ D | p i = x)` in the classical
(Kolmogorov) sense, with no reference to a chosen kernel.

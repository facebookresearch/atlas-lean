# Almost-everywhere formula for an indicator projection

Let `X` be a measurable space,
`μ` any measure on `X`, and `L²(μ)=Lp ℂ 2 μ`, with its Hilbert norm. for a measurable `s ⊆
X` and `f ∈ L²(μ)`, `(indicatorProjection μ s f)(x)=1_s(x) f(x)` for `μ`-almost every `x`.
In Lean this is `indicatorProjection μ s hs f =ᵐ[μ] s.indicator f`.

# C² polynomial approximation on the simplex

Let `U ⊆ ℝⁿ` be an open set containing the simplex
`Δ = {x ∈ ℝⁿ | xᵢ ≥ 0 for all i, ∑ᵢ xᵢ ≤ 1}` (the frequency simplex of `n + 1` alleles), and let
`f` be `C²` on `U`. For every `ε > 0` there is a real polynomial `p` in `n` variables such that at
every point `x ∈ Δ` and for all `i, j`: `|p(x) - f(x)| ≤ ε`, `|∂ᵢ p(x) - ∂ᵢ f(x)| ≤ ε` and
`|∂ᵢ ∂ⱼ p(x) - ∂ᵢ ∂ⱼ f(x)| ≤ ε`, with the formal partial derivatives of `p`. This is the
[approximation on a compact set](exists-mv-polynomial-near-cont-diff-on-t.md) applied to the
compact set `Δ`.

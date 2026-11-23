# SKAT-O minimum p-value over a finite grid of ρ

For a real `n × q` covariate matrix `X`, a real `n × n` matrix `V`, a real `n × m` genotype matrix
`G`, variant weights `a ∈ ℝᵐ`, a nonempty finite set (the grid) of real numbers `ρ` and a phenotype
`y ∈ ℝⁿ`, the SKAT-O statistic is the smallest of the [SKAT-O p-values](skat-opvalue.md) over the
grid,

`T(y) = min_{ρ ∈ grid} p_ρ(y)`

(Lee, Wu and Lin 2012, §2.2). The grid may contain any real numbers; Lee, Wu and Lin take it in
`[0, 1]`. When `Xᵀ V⁻¹ X` is invertible, `T` obeys the [Bonferroni bound](measure-skat-omin-p-le.md)
`ℙ₀(T ≤ t) ≤ |grid| t` for every `t ∈ [0, 1]`, where `ℙ₀` is the null law `y ~ N(X α, V)` for any
`α`: the Gaussian law with mean `X α` and covariance `V` when `V` is positive semidefinite, the
point mass at `X α` otherwise.

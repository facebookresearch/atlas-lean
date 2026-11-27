# Product-form law conditioned on a set of states

Let `S` be a finite set, `c ∈ ℝ^S` and `Γ ⊆ ℕ^S`. The product-form law conditioned on `Γ` is the
function on `ℕ^S` given by `π_c(x | Γ) = π_c(x) / π_c(Γ)` for `x ∈ Γ` and `π_c(x | Γ) = 0` for
`x ∉ Γ`, where `π_c(x)` is the
[Poisson weight](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/poisson-weight.md)
of `x` and `π_c(Γ) = ∑_{y ∈ Γ} π_c(y)` the [mass of the set](class-mass.md). It is defined for every
real `c` and every `Γ`. With the convention `y / 0 = 0` it is identically `0` when `π_c(Γ) = 0`: for
`Γ = ∅`, for a nonempty `Γ` of states of weight `0`, and for some nonempty `Γ` when `c` has a
negative coordinate.

For `c > 0` and nonempty `Γ` its values [sum to one](has-sum-conditioned-law.md) over `ℕ^S`. For
every `c ≥ 0` it is the [conditional probability](cond-poisson-pmf-singleton.md) of a state given
`Γ` under the [product-form Poisson law](poisson-pmf.md). When `c` has a negative coordinate it can
take negative values.

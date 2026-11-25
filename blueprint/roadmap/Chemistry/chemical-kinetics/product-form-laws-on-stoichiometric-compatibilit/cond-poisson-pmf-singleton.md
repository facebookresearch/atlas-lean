# The conditioned law is a conditional probability under the Poisson law

Let `S` be a finite set, `c ∈ ℝ^S` with `c_s ≥ 0` for every `s`, and `μ` the
[product-form Poisson law](poisson-pmf.md) with means `c`, as a probability measure on `ℕ^S`. For
every set `Γ ⊆ ℕ^S` and every state `x`, the conditional probability of `{x}` given `Γ` is the
[conditioned law](conditioned-law.md): `μ({x} | Γ) = π_c(x | Γ)`. Here `μ(· | Γ) = μ(Γ)⁻¹ μ(· ∩ Γ)`
is the zero measure when `μ(Γ) = 0`, and then both sides are `0`. Otherwise `μ(Γ) = π_c(Γ) > 0`, and
both sides are `π_c(x) / π_c(Γ)` for `x ∈ Γ` and `0` for `x ∉ Γ`.

# For positive means and a nonempty set, the conditioned law sums to one

Let `S` be a finite set, `c ∈ ℝ^S` with `c_s > 0` for every `s`, and `Γ ⊆ ℕ^S` a set containing some
state `x₀`. Then the [conditioned law](conditioned-law.md) sums to `1` over all states:
`∑_{x ∈ ℕ^S} π_c(x | Γ) = 1`. Its values are `π_c(x) / π_c(Γ) > 0` on `Γ` and `0` off `Γ`, so it is
a probability mass function on `ℕ^S` carried by `Γ`. The set must be nonempty: for `Γ = ∅` the
conditioned law is identically `0`, by the convention `y / 0 = 0`.

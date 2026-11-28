# A product of one-variable Gaussian sums

For real numbers `a₁, …, a_g` and
`b ∈ ℝ^g`,
`∑_{n ∈ ℤ^g} exp(-∑ᵢ aᵢ(nᵢ + bᵢ)²) = ∏ᵢ ∑_{nᵢ ∈ ℤ} exp(-aᵢ(nᵢ + bᵢ)²)`.
When every `aᵢ > 0` all the series converge (`Javanpeykar.summable_exp_neg_sum_mul_add_sq`); the
identity, as stated here for the values Lean assigns to series, needs no sign condition on the
`aᵢ` (if some series diverges, both sides are `0`).

A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number
Theory 8 (2014), proof of Lemma 2.4.2, p. 101, the second inequality of the display, used with
`aᵢ = π c(g) Im(τ)ᵢᵢ`.

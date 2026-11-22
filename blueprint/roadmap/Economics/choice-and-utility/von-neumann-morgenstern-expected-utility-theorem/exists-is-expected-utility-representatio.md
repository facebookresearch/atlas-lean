# Existence of an expected-utility representation

Expected-utility theorem for finitely many outcomes. Let `≿` be a complete and transitive relation
on the lotteries (probability vectors) over a finite set `X` of outcomes that satisfies independence
(`p ≿ q ⟺ α p + (1 - α) r ≿ α q + (1 - α) r` for all `p`, `q`, `r` and `α ∈ (0, 1]`) and the
Archimedean property (if `p ≻ q ≻ r`, then `α p + (1 - α) r ≻ q ≻ β p + (1 - β) r` for some
`α, β ∈ (0, 1)`). Then some `u : X → ℝ` represents it: `p ≿ q ⟺ ∑ₓ p(x) u(x) ≥ ∑ₓ q(x) u(x)`.

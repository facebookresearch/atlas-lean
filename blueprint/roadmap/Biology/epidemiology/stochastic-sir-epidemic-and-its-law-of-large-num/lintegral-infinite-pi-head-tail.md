# Tonelli formula over an i.i.d. sequence, split into head and tail

Let `μ` be a probability measure on a measurable space `α`, and let `μ^ℕ` be the infinite product
measure on the space `α^ℕ` of sequences `f = (f 0, f 1, …)` in `α`: the law of an i.i.d. sequence
with marginal `μ`. For every function `G : α × α^ℕ → [0, ∞]` that is measurable for the product
σ-algebras,

`∫ G(f 0, tail f) dμ^ℕ(f) = ∫ (∫ G(a, f) dμ^ℕ(f)) dμ(a)`,

where `tail f = (f 1, f 2, …)` is the [tail](seq-tail.md) of `f`. The integrals are Lebesgue
integrals of nonnegative functions, with values in `[0, ∞]`, so no integrability is needed. The
formula follows from the [joint law of the head and the tail](infinite-pi-map-head-tail.md) and
Tonelli's theorem.

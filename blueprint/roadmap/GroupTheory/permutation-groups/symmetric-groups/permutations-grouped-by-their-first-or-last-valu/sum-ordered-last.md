# Summing permutations by their last value

Let `T` be a commutative additive monoid, `n : ℕ`, and `f : S_(n+1) → T`. Then `∑ σ ∈ S_(n+1),
f σ = ∑ i : Fin(n+1), ∑ π ∈ S_n, f(orderedLast i π)`.

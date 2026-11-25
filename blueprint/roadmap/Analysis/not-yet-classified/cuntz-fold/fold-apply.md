# Fold apply

Let `S` be a monoid. Let `R` be a semiring. Let `ι` be a finite index type with decidable equality.
The star on `R` is an additive involution reversing products. `S` acts on `R` preserving addition
and zero. The `S`-scalar action on `R` is compatible with multiplication on both sides. For `v : ι →
R` and `X : CStarMatrix ι ι R`. Assume `∀ i j : ι, star (v i) * v j = if i = j then 1 else 0` and
`(∑ i : ι, v i * star (v i)) = 1`. The fold evaluates to its ordered double sum.

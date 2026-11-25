# Fold symm map

Let `S` be a commutative semiring. Let `R` be a semiring. Let `T` be a semiring. Let `ι` be a finite
index type with decidable equality. The star on `R` is an additive involution reversing products.
`R` is an algebra over `S`. The star on `T` is an additive involution reversing products. `T` is an
algebra over `S`. For `f : R →⋆ₐ[S] T`, `v : ι → R`, `w : ι → T` and `z : R`. Assume `∀ i j : ι,
star (v i) * v j = if i = j then 1 else 0`, `(∑ i : ι, v i * star (v i)) = 1`, `∀ i j : ι, star (w
i) * w j = if i = j then 1 else 0`, `(∑ i : ι, w i * star (w i)) = 1` and `∀ i : ι, w i = f (v i)`.
Every inverse matrix entry is the coefficient image of the source sandwich entry.

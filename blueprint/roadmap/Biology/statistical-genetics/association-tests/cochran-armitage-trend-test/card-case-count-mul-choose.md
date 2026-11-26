# Two-sample counting identity

Let `ι` be a finite set of classes, `R, S ∈ ℕ` and `r, n : ι → ℕ` counts with `∑ᵢ rᵢ = R`. Let `A`
be the number of vectors `z` of length `R + S` with entries in `ι` and
[class counts](class-count.md) `n` whose first `R` entries have class counts `r`, and `B` the number
of all vectors of length `R + S` with class counts `n`. Then `A · C(R + S, R) = (∏ᵢ C(nᵢ, rᵢ)) · B`.
When such vectors exist, that is when `∑ᵢ nᵢ = R + S`, the fraction `A / B` of them whose first `R`
entries have class counts `r` is `∏ᵢ C(nᵢ, rᵢ) / C(R + S, R)`.

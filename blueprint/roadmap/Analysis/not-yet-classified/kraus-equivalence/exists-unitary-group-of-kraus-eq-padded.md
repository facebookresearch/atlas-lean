# Unitary equivalence after zero-padding Kraus families

For finite decidable index types
`n,m,r,s`, suppose `K : r → Matrix m n ℂ` and `L : s → Matrix m n ℂ` define the same completely
positive map. Place `K` on the `r` summand of `r ⊕ s` and zero on `s`, and place `L` on `s` and zero
on `r`. A unitary complex matrix on `r ⊕ s` transforms the first padded family into the second by
`L'ⱼ = ∑ i, U(j,i) K'ᵢ`, without conjugation on coefficients. Empty family and matrix index types
are allowed.

## Sources

- John Watrous, *The Theory of Quantum Information*, Theorem 2.12 and Corollary 2.23.

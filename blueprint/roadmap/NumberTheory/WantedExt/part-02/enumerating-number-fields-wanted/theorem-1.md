---
article_id: af_ed3c5864f734de4163126d16
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.EnumeratingNumberFieldsWanted.EnumeratingNumberFields.theorem_1
---

# Theorem 1

Statement of Theorem 1 (Number fields have small models):

There exists a positive constant `Q` such that the following is true. Let `K` be a number field
of degree `n ≥ Q` and root discriminant `δ` over `ℚ`. Then there exist integers `r ≤ Q log n` and
`d ≤ Q log n` such that `(d + r) choose r ≤ Q n log n`, and there exist `r` polynomials
`E₁, ..., Eᵣ` of degree `≤ d` in `ℤ[x₁, ..., xᵣ]` all having coefficients bounded in absolute value
by `(n δ) ^ (Q log n)` such that the (smooth and zero-dimensional affine) scheme with equations
`E₁ = ... = Eᵣ = 0` and `det (∂Eᵢ/∂xⱼ) ≠ 0` contains `Spec K` as one of its irreducible components.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.EnumeratingNumberFieldsWanted](../../../../../sources/v2/WantedExt.md)
- J.-M. Couveignes, `Enumerating number fields`, Annals of Math, 192 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-2-EnumeratingNumberFields.lean Via leanprover/lean-eval@38361be, problem `annals_enumerating_number_fields`.

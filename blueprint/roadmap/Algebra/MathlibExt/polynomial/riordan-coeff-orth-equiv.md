---
article_id: af_58142ab8749c565b9f8cc8d4
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.riordan_coeff_orth_equiv
---

# Riordan Orthogonal Polynomials

Riordan characterization of coefficient arrays of monic orthogonal polynomials:
for a Riordan array `L = (d, h)`, being the coefficient array of a family of
monic orthogonal polynomials is equivalent to each of: the Meixner-type
`(d, h)`-form with nonzero recurrence subdiagonal; the Stieltjes
production-matrix form of the inverse array with the monic normalization
`L 0 0 = 1`; and the coefficient recurrence form with the same nondegeneracy
condition.

Proof: The coefficient recurrence is the common hub. The Meixner equivalence follows from
Barry-Hennessy, the orthogonality equivalence from Favard's theorem as in Chihara, and the
inverse-array equivalence from the `linvOf` Stieltjes production construction.

## Depends on

- [Formal Orthogonality](is-formally-orthogonal.md)
- [Stieltjes Matrix](../../../LinearAlgebra/MathlibExt/matrix/part-02/stieltjes-matrix/stieltjes-matrix.md)

## Proof depends on

- [Favard Iff](favard-iff.md)

## Sources

- [MathlibExt, MathlibExt.Algebra.Polynomial.RiordanOrthogonalPolynomials](../../../../sources/v2/MathlibExt.md)
- Paul Barry and Aoife Hennessy, "Meixner-Type Results for Riordan Arrays and Associated Integer Sequences," Journal of Integer Sequences 13 (2010), Article 10.9.4, Proposition (referee's summary of the main results), lines 733–752, https://cs.uwaterloo.ca/journals/JIS/VOL13/Barry5/barry96s.tex

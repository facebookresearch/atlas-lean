---
article_id: af_d4172147ab7983e5dc8afeef
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.LinearAlgebra.DiagonalizationWanted.exists_diagonal_similar_of_splits_of_squarefree_minpoly
---

# Exists diagonal similar of splits of squarefree minpoly

A square matrix whose characteristic polynomial splits and whose minimal polynomial is
squarefree is similar to a diagonal matrix.

Proof: a squarefree minimal polynomial makes `Matrix.toLin' A` semisimple, so it has an eigenbasis
by `exists_eigenbasis_of_isSemisimple_of_splits`; conjugating by the change-of-basis matrix from
the standard basis gives the diagonal form.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Diagonalization](../../../../sources/v2/MathlibExt.md)
- Mathlib `docs/undergrad.yaml`, Linear algebra / Structure theory of endomorphisms / diagonalization; R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University Press (2013), Theorem 1.3.12.

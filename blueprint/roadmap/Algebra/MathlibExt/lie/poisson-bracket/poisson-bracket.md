---
article_id: af_8ae4757f694cad88db72ffd9
declaration: structure
origin: cited
statement: formalized
lean: MathlibExt.Algebra.Lie.PoissonBracket.PoissonBracket
---

# Poisson Bracket

Poisson-bracket data: the bracket with bilinearity, skew-symmetry,
the Leibniz rule, the Jacobi identity, and `ℂ`-bilinearity over a
complex algebra structure. (Design note: the laws are carried
explicitly rather than via Mathlib's Lie classes because Mathlib has
no `PoissonAlgebra` class, and combining `LieRing`/`LieAlgebra` with
`CommRing` on one carrier creates `Add`/`Zero` instance diamonds
under which Mathlib's `lie_add`/`lie_zero` no longer rewrite ring
expressions.)

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Algebra.Lie.PoissonBracket](../../../../../sources/v2/MathlibExt.md)

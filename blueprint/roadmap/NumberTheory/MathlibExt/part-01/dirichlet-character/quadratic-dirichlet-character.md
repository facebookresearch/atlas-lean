---
article_id: af_8ddefb9add467f790c1d68e8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.quadraticDirichletCharacter
---

# Quadratic Dirichlet Character

Quadratic Dirichlet character attachment from the source contract.

## Depends on

- [Is Fundamental Discriminant](quadratic/is-fundamental-discriminant.md)
- [Kronecker Sym](quadratic/kronecker-sym.md)

## Proof depends on

- [Kronecker At Prime](quadratic/kronecker-at-prime.md)
- [Kronecker At Two](quadratic/kronecker-at-two.md)
- [Quadratic Character Aux](kronecker-sym-eq-jacobi-sym-of-prime-ne.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.DirichletCharacter.QuadraticDirichletCharacter](../../../../../sources/v2/MathlibExt.md)
- Joshua Males, Andreas Mono, Larry Rolen, and Ian Wagner, *Central L-values of newforms and local polynomials*, `arXiv:2306.15519v5`, subsection "L-functions and L-values", physical line 455. Exact source sentence: "One may also consider L-functions associated to a Dirichlet character chi_D = (D / dot), namely ...". Stable ID: `candidate:a:ef6cab2596e5dbf9`. This is the existence and uniqueness of the integer-valued Dirichlet character of level `Int.natAbs D` evaluating as the positive-denominator Kronecker symbol `kroneckerSym D` at every natural `n`, assuming `IsFundamentalDiscriminant D`. No primitivity or conductor claim belongs to this item.

---
article_id: af_b64ab20ab311a636cff560c1
declaration: inductive
origin: cited
statement: formalized
lean: MetaMathlibExt.IsFreeLieMonomial
---

# Is Free Lie Monomial

A homogeneous Lie monomial in the canonical generators of
`FreeLieAlgebra K (Fin r)`, indexed by its multidegree.

A canonical generator `i` is a monomial whose multidegree is `1` at `i` and
`0` elsewhere; the Lie bracket of monomials of multidegrees `a` and `b` is a
monomial of pointwise multidegree `fun i => a i + b i`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Algebra.Lie.FreeLieMultihomogeneousComponent](../../../../../sources/v2/MathlibExt.md)

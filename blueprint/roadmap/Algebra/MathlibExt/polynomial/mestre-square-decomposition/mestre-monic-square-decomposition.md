---
article_id: af_e9ca3800ebbb917c45d73b23
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.mestre_monic_square_decomposition
---

# Mestre monic square decomposition

Specialized Mestre square decomposition (Arvind Suresh, "Constructing curves
of high rank via composite polynomials", arXiv:2102.02113v2,
<https://arxiv.org/abs/2102.02113>, TeX lines 1158-1179,
Lemma `lem:sqroot`): the section assumes the coefficient field has characteristic
different from 2; the generic monic `m` has degree `2 * d + 2`, the square-root
polynomial `q` is monic of degree `d + 1`, and the remainder `h` has degree at most
`d`, with coefficient comparison inducing a `k`-algebra isomorphism. Hence every
monic `P` of degree `2 * d + 2` over such a field decomposes uniquely as
`P = Q ^ 2 - R` with `Q` monic of degree `d + 1` and `R` of degree at most `d`.
It follows from `mestre_monic_square_decomposition_general`; the hypothesis `hd` is unused
and keeps the source's shape.
Proves `Wanted` entry `mestre_monic_square_decomposition`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Mestre monic square decomposition general](mestre-monic-square-decomposition-genera.md)

## Sources

- [MathlibExt, MathlibExt.Algebra.Polynomial.MestreSquareDecomposition](../../../../../sources/v2/MathlibExt.md)

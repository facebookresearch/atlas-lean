---
article_id: af_b2bae96419d567109630003a
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.partialBellPolynomial
---

# Partial Bell Polynomial

The partial Bell polynomial `B_(n,k)` over a commutative semiring.

The vector `m` records multiplicities of blocks of sizes `1, ..., n+1`.
It is restricted by `∑ i * m_i = n` and `∑ m_i = k`; the source summand
is `n! * ∏ (x_i / i!)^m_i / m_i!`. Stable source identifier:
concept `jis_sem_a0ee8baeec8938655a1c8c9a`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.PartialBellPolynomial](../../../../../../sources/v2/MathlibExt.md)

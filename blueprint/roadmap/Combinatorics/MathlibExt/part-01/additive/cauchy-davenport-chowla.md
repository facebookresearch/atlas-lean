---
article_id: af_d8b64af2cee4733a67b4c480
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Combinatorics.Additive.CauchyDavenportChowlaWanted.cauchy_davenport_chowla
---

# Cauchy Davenport Chowla

If `A` and `B` are nonempty subsets of `ZMod q`, zero belongs to `B`, and
every nonzero member of `B` is a unit, then
`|A + B| ≥ min(q, |A| + |B| - 1)`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Additive.CauchyDavenportChowla](../../../../../sources/v2/MathlibExt.md)
- R. C. Vaughan, *The Hardy–Littlewood Method*, 2nd ed., Cambridge Tracts in Mathematics 125, Cambridge University Press, 1997, Lemma 2.14; also stated as Lemma 3.5 in H. Wang and S. Tian, arXiv:2608.12397v1. Mathlib's `ZMod.cauchy_davenport` covers the prime-modulus special case.

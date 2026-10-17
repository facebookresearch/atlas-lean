---
article_id: af_95ba92c1cf62d2c598a9ea47
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.skolemMahlerLech
---

# Skolem Mahler Lech

Skolem–Mahler–Lech theorem: a linear recurrence sequence over a field of
characteristic zero has zero set equal to a finite union of a finite set and
finitely many full arithmetic progressions.

Proof: Lech's `p`-adic method. The data embed in `ℤ_[p]` for a suitable prime `p`
(Cassels-type embedding), each residue class modulo the period of the companion matrix
mod `p` is a convergent `p`-adic power series, and Strassmann's theorem bounds its zeros.
C. Lech, A note on recurring series, Ark. Mat. 2 (1953), 417–421; J. W. S. Cassels,
An embedding theorem for fields, Bull. Austral. Math. Soc. 14 (1976), 193–198.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Strassmann](../../../part-01/padics/strassmann.md)
- [Cassels Embedding](../../../part-01/padics/exists-injective-ring-hom-closure-padic.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Recurrences.SkolemMahlerLech](../../../../../../sources/v2/MathlibExt.md)
- https://en.wikipedia.org/wiki/Skolem%E2%80%93Mahler%E2%80%93Lech_theorem (statement id `skolem-lech-s1`).

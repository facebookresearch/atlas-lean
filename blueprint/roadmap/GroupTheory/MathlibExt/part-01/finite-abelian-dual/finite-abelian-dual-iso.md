---
article_id: af_6ead723d11e402387d95834a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.GroupTheory.FiniteAbelianDualWanted.finite_abelian_dual_iso
---

# Finite abelian dual iso

A finite abelian group is (non-canonically) isomorphic to its dual group.

Proof: Use the finite abelian structure theorem, apply `AddChar.zmodAddEquiv`
coordinatewise on the cyclic factors, and transport characters along the
decomposition. This is the proof of Conrad's Theorem 3.13: the cyclic case,
then products of cyclic groups.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.GroupTheory.FiniteAbelianDual](../../../../../sources/v2/MathlibExt.md)
- `undergrad.yaml`, section "Representation theory of finite groups", entry "dual groups"; K. Conrad, Characters of finite abelian groups, https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf, Theorem 3.13.

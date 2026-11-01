---
article_id: af_fc5936404d2aeafead9cbb21
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.GroupTheory.FiniteAbelianDualWanted.dual_prod
---

# Dual prod

The dual of a product is the product of the duals.

Proof: Restrict a character along the two coordinate inclusions, with inverse
`(χ₁, χ₂) ↦ fun (x, y) ↦ χ₁ x * χ₂ y`. Conrad's Lemma 3.12 uses the same
restriction map for finite groups and concludes by counting; the explicit
inverse removes the finiteness assumption.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.GroupTheory.FiniteAbelianDual](../../../../../sources/v2/MathlibExt.md)
- `undergrad.yaml`, section "Representation theory of finite groups", entry "dual groups"; K. Conrad, Characters of finite abelian groups, https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf, Lemma 3.12.

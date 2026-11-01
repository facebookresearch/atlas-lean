---
article_id: af_7ee86b164b8d6923c77a276a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Geometry.Manifold.ComplexRigidityWanted.holomorphic_identity_on_connected_complex_manifold
---

# Holomorphic identity on connected complex manifold

If `M` is connected and `f, g : M → F` are `MDiff` and agree on a nonempty open `U ⊂ M`, then `f =
g`. Source: O. Forster, Lectures on Riemann Surfaces, identity theorem for holomorphic maps; Lean
states connected-complex-manifold vector-valued form.
It is `MDifferentiable.eq_of_eqOn_of_isOpen`, kept under the source's name.
Proves `Wanted` entry `holomorphic_identity_on_connected_complex_manifold`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Eq of eq On of is Open](eq-of-eq-on-of-is-open.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Manifold.HolomorphicIdentity](../../../../../../sources/v2/MathlibExt.md)

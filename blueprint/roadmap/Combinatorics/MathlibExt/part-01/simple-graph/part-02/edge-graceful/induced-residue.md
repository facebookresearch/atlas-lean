---
article_id: af_0bfc42be5b14bdf3d4490c4a
declaration: def
origin: cited
statement: formalized
lean: SimpleGraph.inducedResidue
---

# Induced Residue

Induced vertex residue in `Fin (Fintype.card V)`. When the card is zero
there is no modulo to evaluate: map through `Fintype.equivFin V` and eliminate
the resulting `Fin 0`. Thus the empty graph gets the canonical empty vertex
bijection.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Incident Sum](incident-sum.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.SimpleGraph.EdgeGraceful](../../../../../../../sources/v2/MathlibExt.md)

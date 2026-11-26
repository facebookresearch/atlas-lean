# Mem boundary Edges iff

The reduced boundary edges are exactly those with nonzero net integer coefficient.

```lean
theorem mem_boundaryEdges_iff (D : GridFilling) (e : GridEdge) :
    e ∈ D.boundaryEdges ↔ D.boundaryCoeff e ≠ 0
```

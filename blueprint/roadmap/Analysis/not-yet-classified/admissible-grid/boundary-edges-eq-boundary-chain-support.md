# Boundary Edges eq boundary Chain support

The reduced boundary-edge set is exactly the support of the signed boundary chain.

```lean
theorem boundaryEdges_eq_boundaryChain_support (D : GridFilling) :
    D.boundaryEdges = D.boundaryChain.support
```

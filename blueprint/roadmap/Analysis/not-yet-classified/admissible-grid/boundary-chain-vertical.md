# Boundary Chain vertical

The summed boundary chain has the left-minus-right cell coefficient on each vertical edge.

```lean
theorem boundaryChain_vertical (D : GridFilling) (v : GridIndex) :
    D.boundaryChain (.vertical v) = D.boundaryCoeff (.vertical v)
```

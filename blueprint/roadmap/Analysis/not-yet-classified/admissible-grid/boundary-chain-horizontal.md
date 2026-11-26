# Boundary Chain horizontal

The summed boundary chain has the above-minus-below cell coefficient on each horizontal edge.

```lean
theorem boundaryChain_horizontal (D : GridFilling) (v : GridIndex) :
    D.boundaryChain (.horizontal v) = D.boundaryCoeff (.horizontal v)
```

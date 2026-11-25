# Vertical boundary Coeff eq zero iff

A vertical edge cancels exactly when its adjacent cell indicators agree.

```lean
theorem vertical_boundaryCoeff_eq_zero_iff (D : GridFilling) (v : GridIndex) :
    D.boundaryCoeff (.vertical v) = 0 ↔
      D.cellCoeff (v.pred 0) = D.cellCoeff v
```

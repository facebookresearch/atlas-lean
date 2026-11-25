# Horizontal boundary Coeff eq zero iff

A horizontal edge cancels exactly when its adjacent cell indicators agree.

```lean
theorem horizontal_boundaryCoeff_eq_zero_iff (D : GridFilling) (v : GridIndex) :
    D.boundaryCoeff (.horizontal v) = 0 ↔
      D.cellCoeff v = D.cellCoeff (v.pred 1)
```

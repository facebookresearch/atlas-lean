# To Cycle integral eq reduced Integral

Algebraic discrete Stokes: summing the rectangle boundaries of all
selected cells gives exactly the integral over the reduced oriented edge
chain.

```lean
theorem toCycle_integral_eq_reducedIntegral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) (f : ℂ → E) :
    D.toCycle.integral f = D.reducedIntegral f
```

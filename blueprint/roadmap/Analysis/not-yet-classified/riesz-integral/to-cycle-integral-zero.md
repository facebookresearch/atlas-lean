# To Cycle integral zero

The integral of the zero complete Banach-valued function over any filling cycle is zero.

```lean
theorem toCycle_integral_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (D : GridFilling) :
    D.toCycle.integral (0 : ℂ → E) = 0
```

# To Cycle integral eq zero of has Deriv At

The integral of a complex derivative around a reduced grid boundary is
zero.  Only the reduced trace is involved: no differentiability in the
interior of the filling is required.

```lean
theorem toCycle_integral_eq_zero_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) {F f : ℂ → E}
    (hf : ContinuousOn f D.reducedTrace)
    (hF : ∀ z ∈ D.reducedTrace, HasDerivAt F (f z) z) :
    D.toCycle.integral f = 0
```

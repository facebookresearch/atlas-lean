# Riesz Integral congr of eq On reduced Trace

On a fixed reduced grid contour, the Riesz integral depends only on the
values of the scalar function on that contour.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszIntegral_congr_of_eqOn_reducedTrace (D : GridFilling) (a : A)
    {f g : ℂ → ℂ} (hfg : Set.EqOn f g D.reducedTrace) :
    rieszIntegral D.toCycle a f = rieszIntegral D.toCycle a g
```

# Riesz Functional Calculus Linear Map apply

The bundled linear map has the stated functional-calculus value.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszFunctionalCalculusLinearMap_apply (a : A)
    (f : HolomorphicNearSpectrum a) :
    rieszFunctionalCalculusLinearMap a f = rieszFunctionalCalculus a f
```

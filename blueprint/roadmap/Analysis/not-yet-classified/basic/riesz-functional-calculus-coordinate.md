# Riesz Functional Calculus coordinate

the coordinate-function normalization: the Riesz functional calculus sends the coordinate
germ to the Banach-algebra element.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszFunctionalCalculus_coordinate (a : A) :
    rieszFunctionalCalculus a (HolomorphicNearSpectrum.coordinate a) = a
```

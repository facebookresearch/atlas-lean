# Riesz Functional Calculus mul

The Riesz functional calculus preserves multiplication in the displayed order, including for a
noncommutative target algebra.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszFunctionalCalculus_mul (a : A)
    (f g : HolomorphicNearSpectrum a) :
    rieszFunctionalCalculus a (f * g) =
      rieszFunctionalCalculus a f * rieszFunctionalCalculus a g
```

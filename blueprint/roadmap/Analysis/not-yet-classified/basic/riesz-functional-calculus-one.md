# Riesz Functional Calculus one

the constant-function normalization: the Riesz functional calculus sends the constant-one
germ to the identity of the Banach algebra.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszFunctionalCalculus_one (a : A) :
    rieszFunctionalCalculus a (1 : HolomorphicNearSpectrum a) = 1
```

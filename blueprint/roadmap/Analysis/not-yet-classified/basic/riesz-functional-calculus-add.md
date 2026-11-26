# Riesz Functional Calculus add

The Riesz functional calculus preserves addition of holomorphic germs.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszFunctionalCalculus_add (a : A)
    (f g : HolomorphicNearSpectrum a) :
    rieszFunctionalCalculus a (f + g) =
      rieszFunctionalCalculus a f + rieszFunctionalCalculus a g
```

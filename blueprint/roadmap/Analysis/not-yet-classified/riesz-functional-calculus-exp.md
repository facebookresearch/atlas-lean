# Exponential

The Riesz functional calculus of the entire scalar exponential germ is the
ordinary Banach-algebra exponential.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszFunctionalCalculus_exp (a : A) :
    rieszFunctionalCalculus a
        (HolomorphicNearSpectrum.ofFunction a NormedSpace.exp
          (fun z _ => NormedSpace.exp_analytic z)) =
      NormedSpace.exp a
```

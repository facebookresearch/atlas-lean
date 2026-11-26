# Differentiable On analytic Domain

The chosen representative is complex differentiable throughout its analytic domain.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.differentiableOn_analyticDomain (a : A)
    (f : HolomorphicNearSpectrum a) :
    DifferentiableOn ℂ (f.rep a) (f.analyticDomain a)
```

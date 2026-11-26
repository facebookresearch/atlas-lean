# Is Open analytic Domain

The representative analytic domain is open.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.isOpen_analyticDomain (a : A)
    (f : HolomorphicNearSpectrum a) : IsOpen (f.analyticDomain a)
```

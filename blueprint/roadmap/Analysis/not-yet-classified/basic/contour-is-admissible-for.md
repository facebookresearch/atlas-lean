# Contour is Admissible For

The chosen contour has reduced trace in the analytic domain outside the spectrum, index one on
the spectrum and index zero outside the domain.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem HolomorphicNearSpectrum.contour_isAdmissibleFor (a : A)
    (f : HolomorphicNearSpectrum a) :
    (f.contour a).IsAdmissibleFor (spectrum ℂ a) (f.analyticDomain a)
```

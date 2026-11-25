# Riesz Integral eq of is Admissible For

Two admissible grid fillings around the spectrum have equal Riesz integrals for a scalar
function complex differentiable on their common domain.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszIntegral_eq_of_isAdmissibleFor {D E : GridFilling} {a : A}
    {f : ℂ → ℂ} {G : Set ℂ}
    (hD : D.IsAdmissibleFor (spectrum ℂ a) G)
    (hE : E.IsAdmissibleFor (spectrum ℂ a) G)
    (hf : DifferentiableOn ℂ f G) :
    rieszIntegral D.toCycle a f = rieszIntegral E.toCycle a f
```

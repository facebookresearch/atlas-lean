# Riesz Integral id of is Admissible For

An admissible positively oriented grid around the spectrum gives `a` as the Riesz value of the
coordinate function.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszIntegral_id_of_isAdmissibleFor
    {D : GridFilling} {a : A} {G : Set ℂ}
    (hD : D.IsAdmissibleFor (spectrum ℂ a) G) :
    rieszIntegral D.toCycle a id = a
```

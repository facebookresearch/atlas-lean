# Riesz Integral one of is Admissible For

An admissible positively oriented grid around the spectrum gives the algebra identity as the
Riesz value of the constant-one function.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszIntegral_one_of_isAdmissibleFor
    {D : GridFilling} {a : A} {G : Set ℂ}
    (hD : D.IsAdmissibleFor (spectrum ℂ a) G) :
    rieszIntegral D.toCycle a (fun _ : ℂ ↦ 1) = 1
```

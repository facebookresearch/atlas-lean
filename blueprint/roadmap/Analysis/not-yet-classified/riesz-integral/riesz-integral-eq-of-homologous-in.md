# Riesz Integral eq of homologous In

Rectangular-homology form of contour independence: two cycles have the same
Riesz integral when their difference has a rectangle filling in the analytic
resolvent domain.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszIntegral_eq_of_homologousIn {Γ Λ : RectilinearCycle} {a : A}
    {f : ℂ → ℂ} {G : Set ℂ} (hΓΛ : Γ.HomologousIn Λ (G \ spectrum ℂ a))
    (hf : DifferentiableOn ℂ f G) :
    rieszIntegral Γ a f = rieszIntegral Λ a f
```

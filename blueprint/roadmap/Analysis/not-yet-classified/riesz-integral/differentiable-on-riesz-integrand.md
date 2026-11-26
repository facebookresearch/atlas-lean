# Differentiable On riesz Integrand

The Riesz integrand is complex differentiable away from the spectrum on
every domain where the scalar function is complex differentiable.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem differentiableOn_rieszIntegrand {a : A} {f : ℂ → ℂ} {G : Set ℂ}
    (hf : DifferentiableOn ℂ f G) :
    DifferentiableOn ℂ (rieszIntegrand a f) (G \ spectrum ℂ a)
```

# First-moment comparison from cross products

For any measure on ℝ, let f, g and their first-moment functions y f(y), y g(y) be integrable. If (y−z)(f(y)g(z)−f(z)g(y)) is nonnegative for every y and z, then the product of the zeroth moment of f and first moment of g is at most the product of the first moment of f and zeroth moment of g. No positivity, nonzero mass, finiteness of the measure, or probability normalization is assumed.

## Exact statement

```lean
theorem firstMoment_mul_integral_le {μ : Measure ℝ} {f g : ℝ → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hyf : Integrable (fun y => y * f y) μ) (hyg : Integrable (fun y => y * g y) μ)
    (h : ∀ y z, 0 ≤ (y - z) * (f y * g z - f z * g y)) :
    (∫ y, f y ∂μ) * (∫ y, y * g y ∂μ) ≤ (∫ y, y * f y ∂μ) * (∫ y, g y ∂μ)
```

## Proof

Integrate the cross-product inequality successively in both variables and use linearity of the integrable terms.

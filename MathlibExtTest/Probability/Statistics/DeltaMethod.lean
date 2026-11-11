/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.DeltaMethod
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Tests for the delta method

On `Ω = ℝ` with the standard Gaussian law, `X θ n ω := θ + (n + 1)⁻¹ * ω` satisfies
`(n + 1) * (X θ n - θ) = id` exactly, so the scaled sequence converges in distribution to
`Z := id`. The delta method is applied to `g x = x ^ 2`:

* at `θ = 1` (derivative `2`), giving the limit `2 * Z`, both through the normed-space theorem
  with `L = 2 • id` and through the one-dimensional corollary;
* at `θ = 0` (derivative `0`), the degenerate case, giving the constant limit `0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace MathlibExtTest.Probability.Statistics.DeltaMethod

/-- The scale `r n = n + 1`. -/
noncomputable def r (n : ℕ) : ℝ := n + 1

/-- The scale `n + 1` tends to infinity. -/
theorem r_tendsto : Tendsto r atTop atTop :=
  tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop

/-- `X θ n ω = θ + (n + 1)⁻¹ * ω`. -/
noncomputable def X (θ : ℝ) (n : ℕ) (ω : ℝ) : ℝ := θ + (r n)⁻¹ * ω

/-- `X θ n` is measurable. -/
theorem X_measurable (θ : ℝ) (n : ℕ) : Measurable (X θ n) := by
  unfold X; fun_prop

/-- By construction `(n + 1) * (X θ n - θ) = id`, so the scaled sequence converges in
distribution to `id`. -/
theorem scaled_tendstoInDistribution (θ : ℝ) :
    TendstoInDistribution (fun n ω ↦ r n • (X θ n ω - θ)) atTop id
      (fun _ ↦ gaussianReal 0 1) (gaussianReal 0 1) :=
  (tendstoInDistribution_const (l := atTop) aemeasurable_id).congr
    (fun n ↦ ae_of_all _ fun ω ↦ by
      have : r n ≠ 0 := by unfold r; positivity
      simp [X, this])
    (ae_of_all _ fun _ ↦ rfl)

/-- The same scaled sequence, written with `*`. -/
theorem scaled_tendstoInDistribution_mul (θ : ℝ) :
    TendstoInDistribution (fun n ω ↦ r n * (X θ n ω - θ)) atTop id
      (fun _ ↦ gaussianReal 0 1) (gaussianReal 0 1) :=
  scaled_tendstoInDistribution θ

/-- `x ↦ x ^ 2` has Fréchet derivative `2 • id` at `1`. -/
theorem hasFDerivAt_sq_one :
    HasFDerivAt (fun x : ℝ ↦ x ^ 2) ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) 1 :=
  (hasDerivAt_pow 2 (1 : ℝ)).hasFDerivAt.congr_fderiv (by ext; simp)

/-- Normed-space delta method at `θ = 1`: `(n + 1) • (X n ^ 2 - 1) →ᵈ 2 * Z`. -/
example : TendstoInDistribution (fun n ω ↦ r n • (X 1 n ω ^ 2 - 1 ^ 2)) atTop (fun ω ↦ 2 * ω)
    (fun _ ↦ gaussianReal 0 1) (gaussianReal 0 1) :=
  ((scaled_tendstoInDistribution 1).delta_method (g := fun x ↦ x ^ 2) r_tendsto
    hasFDerivAt_sq_one (fun n ↦ (X_measurable 1 n).aemeasurable)
    (fun n ↦ ((X_measurable 1 n).pow_const 2).aemeasurable)).congr
    (fun _ ↦ ae_of_all _ fun _ ↦ rfl) (ae_of_all _ fun _ ↦ by simp)

/-- One-dimensional corollary at `θ = 1`: `(n + 1) * (X n ^ 2 - 1) →ᵈ 2 * Z`. -/
example : TendstoInDistribution (fun n ω ↦ r n * (X 1 n ω ^ 2 - 1 ^ 2)) atTop (fun ω ↦ 2 * ω)
    (fun _ ↦ gaussianReal 0 1) (gaussianReal 0 1) :=
  ((scaled_tendstoInDistribution_mul 1).delta_method_real (g := fun x ↦ x ^ 2) r_tendsto
    (hasDerivAt_pow 2 1) (fun n ↦ (X_measurable 1 n).aemeasurable)
    (fun n ↦ ((X_measurable 1 n).pow_const 2).aemeasurable)).congr
    (fun _ ↦ ae_of_all _ fun _ ↦ rfl) (ae_of_all _ fun _ ↦ by simp)

/-- Degenerate case `θ = 0`, derivative `0`: the first-order limit is the constant `0`. -/
example : TendstoInDistribution (fun n ω ↦ r n • (X 0 n ω ^ 2 - 0 ^ 2)) atTop (fun _ ↦ 0)
    (fun _ ↦ gaussianReal 0 1) (gaussianReal 0 1) :=
  ((scaled_tendstoInDistribution 0).delta_method (g := fun x ↦ x ^ 2) (L := 0) r_tendsto
    ((hasDerivAt_pow 2 (0 : ℝ)).hasFDerivAt.congr_fderiv (by ext; simp))
    (fun n ↦ (X_measurable 0 n).aemeasurable)
    (fun n ↦ ((X_measurable 0 n).pow_const 2).aemeasurable)).congr
    (fun _ ↦ ae_of_all _ fun _ ↦ rfl) (ae_of_all _ fun _ ↦ rfl)

end MathlibExtTest.Probability.Statistics.DeltaMethod

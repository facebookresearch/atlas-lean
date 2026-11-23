/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.VectorInference
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Godambe's information inequality for estimating functions

Let `s, g : 𝓧 → E` be square-integrable functions into a real inner product space `E` (a score
and an estimating function) under any measure `μ`, and let `I` be an invertible operator with
`⟪I z, z⟫ = E ⟪s, z⟫²` (the Fisher information `E[s sᵀ]`). For every `w`, with
`v = E[⟪g, w⟫ s]`, `⟪I⁻¹ v, v⟫ ≤ E ⟪g, w⟫²`: the information about the parameter carried by the
linear combination `⟪g, w⟫` of the estimating function is at most the Fisher information. The
proof is `0 ≤ E (⟪g, w⟫ - ⟪s, I⁻¹ v⟫)²`. No model structure is assumed; relating `v` to the
derivative of an estimating function (differentiated unbiasedness) is left to applications.

## Main results

* `inner_inverse_le_integral_inner_sq`: Godambe's information inequality.
* `integrable_inner_sq`, `integrable_inner_smul`: the integrability of `⟪f, w⟫²` and of
  `⟪g, w⟫ • f` for square-integrable `f` and `g`, used in the proof and by applications.

## Implementation notes

`Ring.inverse I` is the inverse operator; `apply_inverse_apply` comes from
`MathlibExt.Probability.Statistics.VectorInference`, whose `cramerRao` is the unbiased-estimator
bound, a different statement.

## References

* V. P. Godambe, *An optimum property of regular maximum likelihood estimation*, Ann. Math.
  Statist. 31 (1960), 1208–1211.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace
open MathlibExt.Probability.Statistics.VectorInference (apply_inverse_apply)

namespace MathlibExt.Probability.Statistics.GodambeInequality

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {μ : Measure 𝓧}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If `f` is square integrable, so is each projection `⟪f, w⟫`. -/
theorem integrable_inner_sq {f : 𝓧 → E} (hf_meas : AEStronglyMeasurable f μ)
    (hf_sq : Integrable (fun x => ‖f x‖ ^ 2) μ) (w : E) :
    Integrable (fun x => ⟪f x, w⟫ ^ 2) μ :=
  (hf_sq.mul_const (‖w‖ ^ 2)).mono' ((hf_meas.inner aestronglyMeasurable_const).pow 2)
    (ae_of_all _ fun x => by
      rw [norm_pow, Real.norm_eq_abs, sq_abs, ← mul_pow]
      calc ⟪f x, w⟫ ^ 2 = |⟪f x, w⟫| ^ 2 := (sq_abs _).symm
        _ ≤ (‖f x‖ * ‖w‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2)

/-- If `f` and `g` are square integrable, `⟪g, w⟫ • f` is integrable. -/
theorem integrable_inner_smul {f g : 𝓧 → E} (hf_meas : AEStronglyMeasurable f μ)
    (hf_sq : Integrable (fun x => ‖f x‖ ^ 2) μ) (hg_meas : AEStronglyMeasurable g μ)
    (hg_sq : Integrable (fun x => ‖g x‖ ^ 2) μ) (w : E) :
    Integrable (fun x => ⟪g x, w⟫ • f x) μ :=
  ((integrable_inner_sq hg_meas hg_sq w).add hf_sq).mono'
    ((hg_meas.inner aestronglyMeasurable_const).smul hf_meas)
    (ae_of_all _ fun x => by
      rw [norm_smul, Real.norm_eq_abs]
      change |⟪g x, w⟫| * ‖f x‖ ≤ ⟪g x, w⟫ ^ 2 + ‖f x‖ ^ 2
      nlinarith [sq_nonneg (|⟪g x, w⟫| - ‖f x‖), sq_abs ⟪g x, w⟫, abs_nonneg ⟪g x, w⟫,
        norm_nonneg (f x)])

variable [CompleteSpace E]

/-- **Information inequality for estimating functions** (Godambe 1960). Let `s, g : 𝓧 → E` be
square integrable (a score and an estimating function) and let `I` be the invertible operator
with `⟪I z, z⟫ = E ⟪s, z⟫²` (the Fisher information `E[s sᵀ]`). For every `w`, with
`v = E[⟪g, w⟫ s]`, `⟪I⁻¹ v, v⟫ ≤ E ⟪g, w⟫²`: the information about `θ` carried by the linear
combination `⟪g, w⟫` of the estimating function is at most the Fisher information. The proof is
`0 ≤ E (⟪g, w⟫ - ⟪s, I⁻¹ v⟫)²`.

Source: V. P. Godambe, *An optimum property of regular maximum likelihood estimation*, Ann.
Math. Statist. 31 (1960), 1208–1211. -/
theorem inner_inverse_le_integral_inner_sq {s g : 𝓧 → E} (hs_meas : AEStronglyMeasurable s μ)
    (hs_sq : Integrable (fun x => ‖s x‖ ^ 2) μ) (hg_meas : AEStronglyMeasurable g μ)
    (hg_sq : Integrable (fun x => ‖g x‖ ^ 2) μ) {I : E →L[ℝ] E} (hI : IsUnit I)
    (hI_quad : ∀ z, ⟪I z, z⟫ = ∫ x, ⟪s x, z⟫ ^ 2 ∂μ) (w : E) :
    ⟪Ring.inverse I (∫ x, ⟪g x, w⟫ • s x ∂μ), ∫ x, ⟪g x, w⟫ • s x ∂μ⟫ ≤
      ∫ x, ⟪g x, w⟫ ^ 2 ∂μ := by
  set v := ∫ x, ⟪g x, w⟫ • s x ∂μ
  set z := Ring.inverse I v
  have hIz : I z = v :=
    apply_inverse_apply hI v
  have hgw : AEStronglyMeasurable (fun x => ⟪g x, w⟫) μ :=
    hg_meas.inner aestronglyMeasurable_const
  have hsz : AEStronglyMeasurable (fun x => ⟪s x, z⟫) μ :=
    hs_meas.inner aestronglyMeasurable_const
  have hgw2 := integrable_inner_sq hg_meas hg_sq w
  have hsz2 := integrable_inner_sq hs_meas hs_sq z
  have hprod : Integrable (fun x => ⟪g x, w⟫ * ⟪s x, z⟫) μ :=
    (hgw2.add hsz2).mono' (hgw.mul hsz) (ae_of_all _ fun x => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      change |⟪g x, w⟫| * |⟪s x, z⟫| ≤ ⟪g x, w⟫ ^ 2 + ⟪s x, z⟫ ^ 2
      nlinarith [sq_nonneg (|⟪g x, w⟫| - |⟪s x, z⟫|), sq_abs ⟪g x, w⟫, sq_abs ⟪s x, z⟫])
  have hC : ⟪z, v⟫ = ∫ x, ⟪g x, w⟫ * ⟪s x, z⟫ ∂μ := by
    rw [← integral_inner (integrable_inner_smul hs_meas hs_sq hg_meas hg_sq w) z]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [real_inner_smul_right, real_inner_comm (s x) z]
  have hQ : ∫ x, ⟪s x, z⟫ ^ 2 ∂μ = ⟪z, v⟫ := by rw [← hI_quad, hIz, real_inner_comm]
  have hnonneg : 0 ≤ ∫ x, (⟪g x, w⟫ - ⟪s x, z⟫) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hexp : ∫ x, (⟪g x, w⟫ - ⟪s x, z⟫) ^ 2 ∂μ = ∫ x, ⟪g x, w⟫ ^ 2 ∂μ -
      2 * ∫ x, ⟪g x, w⟫ * ⟪s x, z⟫ ∂μ + ∫ x, ⟪s x, z⟫ ^ 2 ∂μ := by
    have e : ∀ x, (⟪g x, w⟫ - ⟪s x, z⟫) ^ 2 =
        ⟪g x, w⟫ ^ 2 - 2 * (⟪g x, w⟫ * ⟪s x, z⟫) + ⟪s x, z⟫ ^ 2 := fun x => by ring
    simp_rw [e]
    rw [integral_add _ hsz2, integral_sub hgw2 (hprod.const_mul 2), integral_const_mul]
    exact hgw2.sub (hprod.const_mul 2)
  linarith

end MathlibExt.Probability.Statistics.GodambeInequality

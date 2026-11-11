/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

/-
Adapted from `anthropics/fermats-last-theorem` at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`:
Sources in `P2M/Sol/`, with corresponding `Thm_` wrappers in `Theorems/`:
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MeasureTheory_lintegral_enorm_mul_eq_and_integral_mul_eq_of_forall_lintegral_comp_smul_eq_one.lean
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one.lean
The extraction framework is removed. The nonnegative integral argument allows
ENNReal-valued weights; integrability and integral equality are separate APIs.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
The upstream NOTICE also credits Mathlib:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in their file headers.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Normalized cutoffs for measure-preserving actions

An invariant observable has the same weighted integral for any two nonnegative
measurable weights whose orbit integrals are one on its support. The acting
measure is S-finite and inversion-invariant, not necessarily Haar. The action
preserves the S-finite measure on the underlying space.

No topology, compact support, or boundedness is assumed. Integrability is
transported between weights, not asserted without an integrable starting
weight. The complex integral equality also holds when both weighted functions
are nonintegrable, since both Bochner integrals are then zero.
-/

public section

open scoped ENNReal

namespace MeasureTheory

private theorem enorm_mul_ofReal_nonneg {z : ℂ} {r : ℝ} (hr : 0 ≤ r) :
    ‖z * (r : ℂ)‖ₑ = ‖z‖ₑ * ENNReal.ofReal r := by
  rw [enorm_mul]
  congr 1
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hr]

section Action

variable {A X : Type*} [Group A] [MulAction A X]
  [MeasurableSpace A] [MeasurableInv A] [MeasurableSpace X]
  (τ : Measure A) [SFinite τ] [τ.IsInvInvariant]
  (μ : Measure X) [SFinite μ]

/-- Nonnegative integrals of an invariant function agree for orbit-normalized
weights. Normalization is needed only where the function is nonzero, and the
common integral is allowed to be infinite. -/
theorem lintegral_mul_eq_of_normalized_smul
    (hact : Measurable fun p : A × X => p.1 • p.2)
    (hμ : ∀ a : A, MeasurePreserving (fun x : X => a • x) μ μ)
    {f w₁ w₂ : X → ℝ≥0∞} (hf : Measurable f)
    (hfinv : ∀ (a : A) (x : X), f (a • x) = f x)
    (hw₁ : Measurable w₁) (hw₂ : Measurable w₂)
    (h₁ : ∀ x, f x ≠ 0 → ∫⁻ a, w₁ (a • x) ∂τ = 1)
    (h₂ : ∀ x, f x ≠ 0 → ∫⁻ a, w₂ (a • x) ∂τ = 1) :
    ∫⁻ x, f x * w₁ x ∂μ = ∫⁻ x, f x * w₂ x ∂μ := by
  have hactx (x : X) : Measurable fun a : A => a • x :=
    hact.comp (measurable_id.prodMk measurable_const)
  have hacta (a : A) : Measurable fun x : X => a • x :=
    hact.comp (measurable_const.prodMk measurable_id)
  have hF : Measurable fun p : X × A =>
      f p.1 * w₁ p.1 * w₂ (p.2 • p.1) :=
    ((hf.comp measurable_fst).mul (hw₁.comp measurable_fst)).mul
      (hw₂.comp (hact.comp (measurable_snd.prodMk measurable_fst)))
  have hF' : Measurable fun p : A × X =>
      f p.2 * w₁ (p.1⁻¹ • p.2) * w₂ p.2 :=
    ((hf.comp measurable_snd).mul
      (hw₁.comp (hact.comp (measurable_fst.inv.prodMk measurable_snd)))).mul
      (hw₂.comp measurable_snd)
  calc
    ∫⁻ x, f x * w₁ x ∂μ =
        ∫⁻ x, ∫⁻ a, f x * w₁ x * w₂ (a • x) ∂τ ∂μ := by
      refine lintegral_congr fun x => ?_
      have hm : Measurable fun a : A => w₂ (a • x) := hw₂.comp (hactx x)
      rw [lintegral_const_mul _ hm]
      by_cases hx : f x = 0
      · simp [hx]
      · rw [h₂ x hx, mul_one]
    _ = ∫⁻ a, ∫⁻ x, f x * w₁ x * w₂ (a • x) ∂μ ∂τ :=
      lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ a, ∫⁻ x, f x * w₁ (a⁻¹ • x) * w₂ x ∂μ ∂τ := by
      refine lintegral_congr fun a => ?_
      have hm : Measurable fun x : X => f x * w₁ (a⁻¹ • x) * w₂ x :=
        (hf.mul (hw₁.comp (hacta a⁻¹))).mul hw₂
      rw [← (hμ a).lintegral_comp hm]
      refine lintegral_congr fun x => ?_
      simp only [hfinv, inv_smul_smul]
    _ = ∫⁻ x, ∫⁻ a, f x * w₁ (a⁻¹ • x) * w₂ x ∂τ ∂μ :=
      lintegral_lintegral_swap hF'.aemeasurable
    _ = ∫⁻ x, f x * w₂ x * ∫⁻ a, w₁ (a • x) ∂τ ∂μ := by
      refine lintegral_congr fun x => ?_
      have hm : Measurable fun a : A => w₁ (a⁻¹ • x) :=
        hw₁.comp ((hactx x).comp measurable_inv)
      simp_rw [mul_right_comm (f x)]
      rw [lintegral_const_mul _ hm]
      rw [lintegral_inv_eq_self (μ := τ) (fun a : A => w₁ (a • x))]
    _ = ∫⁻ x, f x * w₂ x ∂μ := by
      refine lintegral_congr fun x => ?_
      by_cases hx : f x = 0
      · simp [hx]
      · rw [h₁ x hx, mul_one]

variable {f : X → ℂ} {w₁ w₂ : X → ℝ}

/-- Integrability of an invariant complex function times a nonnegative real
weight is independent of the weight when both orbit averages are one on the
function's support. Neither weighted function is required to be integrable. -/
theorem integrable_mul_iff_of_normalized_smul
    (hact : Measurable fun p : A × X => p.1 • p.2)
    (hμ : ∀ a : A, MeasurePreserving (fun x : X => a • x) μ μ)
    (hf : Measurable f) (hfinv : ∀ (a : A) (x : X), f (a • x) = f x)
    (hw₁ : Measurable w₁) (hw₂ : Measurable w₂)
    (hw₁0 : ∀ x, 0 ≤ w₁ x) (hw₂0 : ∀ x, 0 ≤ w₂ x)
    (h₁ : ∀ x, f x ≠ 0 → ∫⁻ a, ENNReal.ofReal (w₁ (a • x)) ∂τ = 1)
    (h₂ : ∀ x, f x ≠ 0 → ∫⁻ a, ENNReal.ofReal (w₂ (a • x)) ∂τ = 1) :
    Integrable (fun x => f x * (w₁ x : ℂ)) μ ↔
      Integrable (fun x => f x * (w₂ x : ℂ)) μ := by
  have hne (x : X) (hx : ‖f x‖ₑ ≠ 0) : f x ≠ 0 :=
    fun h0 => hx (by rw [h0, enorm_zero])
  have hnorm := lintegral_mul_eq_of_normalized_smul τ μ hact hμ
    (f := fun x => ‖f x‖ₑ) (w₁ := fun x => ENNReal.ofReal (w₁ x))
    (w₂ := fun x => ENNReal.ofReal (w₂ x)) hf.enorm
    (fun a x => by simp only [hfinv])
    (ENNReal.measurable_ofReal.comp hw₁) (ENNReal.measurable_ofReal.comp hw₂)
    (fun x hx => h₁ x (hne x hx)) (fun x hx => h₂ x (hne x hx))
  have hmeas₁ : AEStronglyMeasurable (fun x => f x * (w₁ x : ℂ)) μ :=
    (hf.mul (Complex.measurable_ofReal.comp hw₁)).aestronglyMeasurable
  have hmeas₂ : AEStronglyMeasurable (fun x => f x * (w₂ x : ℂ)) μ :=
    (hf.mul (Complex.measurable_ofReal.comp hw₂)).aestronglyMeasurable
  constructor
  · intro hi
    refine ⟨hmeas₂, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simp_rw [enorm_mul_ofReal_nonneg (hw₂0 _)]
    rw [← hnorm]
    simpa only [enorm_mul_ofReal_nonneg (hw₁0 _)] using
      hasFiniteIntegral_iff_enorm.mp hi.2
  · intro hi
    refine ⟨hmeas₁, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simp_rw [enorm_mul_ofReal_nonneg (hw₁0 _)]
    rw [hnorm]
    simpa only [enorm_mul_ofReal_nonneg (hw₂0 _)] using
      hasFiniteIntegral_iff_enorm.mp hi.2

private theorem lintegral_ofReal_comp_mul_eq
    (hact : Measurable fun p : A × X => p.1 • p.2)
    (hμ : ∀ a : A, MeasurePreserving (fun x : X => a • x) μ μ)
    (hf : Measurable f) (hfinv : ∀ (a : A) (x : X), f (a • x) = f x)
    (c : ℂ → ℝ) (hc : Measurable c) (hc0 : c 0 = 0)
    (hw₁ : Measurable w₁) (hw₂ : Measurable w₂)
    (hw₁0 : ∀ x, 0 ≤ w₁ x) (hw₂0 : ∀ x, 0 ≤ w₂ x)
    (h₁ : ∀ x, f x ≠ 0 → ∫⁻ a, ENNReal.ofReal (w₁ (a • x)) ∂τ = 1)
    (h₂ : ∀ x, f x ≠ 0 → ∫⁻ a, ENNReal.ofReal (w₂ (a • x)) ∂τ = 1) :
    ∫⁻ x, ENNReal.ofReal (c (f x) * w₁ x) ∂μ =
      ∫⁻ x, ENNReal.ofReal (c (f x) * w₂ x) ∂μ := by
  have hne (x : X) (hx : ENNReal.ofReal (c (f x)) ≠ 0) : f x ≠ 0 := by
    intro h0
    exact hx (by rw [h0, hc0, ENNReal.ofReal_zero])
  have h := lintegral_mul_eq_of_normalized_smul τ μ hact hμ
    (f := fun x => ENNReal.ofReal (c (f x)))
    (w₁ := fun x => ENNReal.ofReal (w₁ x))
    (w₂ := fun x => ENNReal.ofReal (w₂ x))
    (ENNReal.measurable_ofReal.comp (hc.comp hf))
    (fun a x => by simp only [hfinv])
    (ENNReal.measurable_ofReal.comp hw₁) (ENNReal.measurable_ofReal.comp hw₂)
    (fun x hx => h₁ x (hne x hx)) (fun x hx => h₂ x (hne x hx))
  simpa only [← ENNReal.ofReal_mul' (hw₁0 _),
    ← ENNReal.ofReal_mul' (hw₂0 _)] using h

/-- Weighted integrals of an invariant complex function agree for nonnegative
orbit-normalized cutoffs. If one weighted function is not integrable, neither
is the other, and both Bochner integrals are zero. -/
theorem integral_mul_eq_of_normalized_smul
    (hact : Measurable fun p : A × X => p.1 • p.2)
    (hμ : ∀ a : A, MeasurePreserving (fun x : X => a • x) μ μ)
    (hf : Measurable f) (hfinv : ∀ (a : A) (x : X), f (a • x) = f x)
    (hw₁ : Measurable w₁) (hw₂ : Measurable w₂)
    (hw₁0 : ∀ x, 0 ≤ w₁ x) (hw₂0 : ∀ x, 0 ≤ w₂ x)
    (h₁ : ∀ x, f x ≠ 0 → ∫⁻ a, ENNReal.ofReal (w₁ (a • x)) ∂τ = 1)
    (h₂ : ∀ x, f x ≠ 0 → ∫⁻ a, ENNReal.ofReal (w₂ (a • x)) ∂τ = 1) :
    ∫ x, f x * (w₁ x : ℂ) ∂μ = ∫ x, f x * (w₂ x : ℂ) ∂μ := by
  have hiff := integrable_mul_iff_of_normalized_smul τ μ hact hμ
    hf hfinv hw₁ hw₂ hw₁0 hw₂0 h₁ h₂
  by_cases hi : Integrable (fun x => f x * (w₁ x : ℂ)) μ
  · have hi₂ := hiff.mp hi
    have key (c : ℂ → ℝ) (hc : Measurable c) (hc0 : c 0 = 0) :=
      lintegral_ofReal_comp_mul_eq τ μ hact hμ hf hfinv c hc hc0
        hw₁ hw₂ hw₁0 hw₂0 h₁ h₂
    have hre (w : X → ℝ) (x : X) :
        RCLike.re (f x * (w x : ℂ)) = Complex.re (f x) * w x := by simp
    have him (w : X → ℝ) (x : X) :
        RCLike.im (f x * (w x : ℂ)) = Complex.im (f x) * w x := by simp
    have hreI {w : X → ℝ} (hw : Integrable (fun x => f x * (w x : ℂ)) μ) :
        ∫ x, RCLike.re (f x * (w x : ℂ)) ∂μ =
          (∫⁻ x, ENNReal.ofReal (Complex.re (f x) * w x) ∂μ).toReal -
            (∫⁻ x, ENNReal.ofReal ((-Complex.re (f x)) * w x) ∂μ).toReal := by
      rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hw.re]
      simp only [hre, neg_mul]
    have himI {w : X → ℝ} (hw : Integrable (fun x => f x * (w x : ℂ)) μ) :
        ∫ x, RCLike.im (f x * (w x : ℂ)) ∂μ =
          (∫⁻ x, ENNReal.ofReal (Complex.im (f x) * w x) ∂μ).toReal -
            (∫⁻ x, ENNReal.ofReal ((-Complex.im (f x)) * w x) ∂μ).toReal := by
      rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hw.im]
      simp only [him, neg_mul]
    rw [← integral_re_add_im hi, ← integral_re_add_im hi₂,
      hreI hi, hreI hi₂, himI hi, himI hi₂,
      key Complex.re Complex.measurable_re Complex.zero_re,
      key (fun z => -Complex.re z) Complex.measurable_re.neg (by simp),
      key Complex.im Complex.measurable_im Complex.zero_im,
      key (fun z => -Complex.im z) Complex.measurable_im.neg (by simp)]
  · rw [integral_undef hi, integral_undef (fun h => hi (hiff.mpr h))]

end Action

/-- Subgroup-normalized nonnegative weights give the same integral of an
invariant complex function. This measure-theoretic statement requires neither
a closed subgroup nor compact supports nor a bounded function. -/
theorem integral_mul_eq_of_normalized_subgroup
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]
    (T : Subgroup G) [MeasurableSpace T] [MeasurableInv T]
    (hT : Measurable (Subtype.val : T → G))
    (τ : Measure T) [SFinite τ] [τ.IsInvInvariant]
    (f : G → ℂ) (hf : Measurable f)
    (hfinv : ∀ (t : T) (x : G), f ((t : G) * x) = f x)
    (w₁ w₂ : G → ℝ) (hw₁0 : ∀ x, 0 ≤ w₁ x) (hw₂0 : ∀ x, 0 ≤ w₂ x)
    (hw₁ : Measurable w₁) (hw₂ : Measurable w₂)
    (h₁ : ∀ x, f x ≠ 0 → ∫ t : T, w₁ ((t : G) * x) ∂τ = 1)
    (h₂ : ∀ x, f x ≠ 0 → ∫ t : T, w₂ ((t : G) * x) ∂τ = 1) :
    ∫ x, f x * (w₁ x : ℂ) ∂μ = ∫ x, f x * (w₂ x : ℂ) ∂μ := by
  have hact : Measurable fun p : T × G => p.1 • p.2 :=
    (hT.comp measurable_fst).mul measurable_snd
  have hμ (t : T) : MeasurePreserving (fun x : G => t • x) μ μ :=
    measurePreserving_mul_left μ (t : G)
  apply integral_mul_eq_of_normalized_smul τ μ hact hμ hf hfinv
    hw₁ hw₂ hw₁0 hw₂0
  · intro x hx
    change ∫⁻ t : T, ENNReal.ofReal (w₁ ((t : G) * x)) ∂τ = 1
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_of_integral_eq_one (h₁ x hx))
      (Filter.Eventually.of_forall fun t => hw₁0 _), h₁ x hx, ENNReal.ofReal_one]
  · intro x hx
    change ∫⁻ t : T, ENNReal.ofReal (w₂ ((t : G) * x)) ∂τ = 1
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_of_integral_eq_one (h₂ x hx))
      (Filter.Eventually.of_forall fun t => hw₂0 _), h₂ x hx, ENNReal.ofReal_one]

end MeasureTheory

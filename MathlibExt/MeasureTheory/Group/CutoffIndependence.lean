/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

/-
Adapted from `anthropics/fermats-last-theorem` at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`:
* Theorem in `Theorems/`:
  `Thm_MeasureTheory_integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one.lean`
* `P2M/Sol/S_MeasureTheory_integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one.lean`
Source: https://github.com/anthropics/fermats-last-theorem
The proof-extraction framework is removed, helpers are private, and the
finite-integral estimate is also exposed as an integrability theorem.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
The upstream NOTICE also credits Mathlib:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in their file headers.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.Integral
import MathlibExt.MeasureTheory.Group.ActionCutoff

/-!
# Independence of normalized subgroup cutoffs

A bounded measurable complex function invariant under the left action of a
closed subgroup has the same integral against any two nonnegative measurable
compactly supported weights normalized along that subgroup on its support.
The subgroup Haar measure must be inversion-invariant; no normality or
discreteness of the subgroup, or right invariance of the ambient Haar measure,
is required.

The weights need not be continuous or bounded. Compact support and
measurability alone do not imply integrability: a positive Tonelli estimate
using subgroup normalization proves it here. Independence follows from the
general measure-preserving action theorem in `ActionCutoff`.
This provides cutoff-independent integrals and pairings of invariant functions.
-/

public section

open Filter Set TopologicalSpace
open scoped ENNReal NNReal Topology

namespace MeasureTheory

private theorem measurable_subgroup_mul
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) [MeasurableSpace T] [BorelSpace T] :
    Measurable fun p : G × T => (p.2 : G) * p.1 :=
  ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).measurable

private theorem enorm_ofReal_of_nonneg {r : ℝ} (hr : 0 ≤ r) :
    ‖(r : ℂ)‖ₑ = ENNReal.ofReal r := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hr]

section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (T : Subgroup G) [MeasurableSpace T] [BorelSpace T]
  (μ : Measure G) (τ : Measure T)

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
private theorem lintegral_fibre_eq_one {w : G → ℝ}
    (hw0 : ∀ x, 0 ≤ w x) (hw : Measurable w) {x : G}
    (h : ∫ t : T, w ((t : G) * x) ∂τ = 1) :
    ∫⁻ t : T, ENNReal.ofReal (w ((t : G) * x)) ∂τ = 1 := by
  have hwm : Measurable (fun t : T => w ((t : G) * x)) :=
    hw.comp (continuous_subtype_val.mul continuous_const).measurable
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun t => hw0 _) hwm.aestronglyMeasurable] at h
  exact (ENNReal.toReal_eq_one_iff _).1 h

variable [μ.IsHaarMeasure] [τ.IsHaarMeasure] [τ.IsInvInvariant]
  (hT : IsClosed (T : Set G))
include hT

omit [μ.IsHaarMeasure] [τ.IsInvInvariant] [MeasurableSpace G] [BorelSpace G]
  [BorelSpace T] in
private theorem sFinite_subgroup_haar : SFinite τ := by
  have : SigmaCompactSpace T := hT.isClosedEmbedding_subtypeVal.sigmaCompactSpace
  infer_instance

/-- A compact neighborhood gives a uniform positive lower bound for its
subgroup average on the support of the weight. Tonelli and normalization
then bound the weighted integral by a finite multiple of its volume. -/
private theorem lintegral_enorm_mul_lt_top (F : G → ℂ) (hFm : Measurable F)
    {C : ℝ} (hFb : ∀ x, ‖F x‖ ≤ C)
    (hFT : ∀ (t : T) (x : G), F ((t : G) * x) = F x)
    (w : G → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hwm : Measurable w)
    (hwc : HasCompactSupport w)
    (hw1 : ∀ x, F x ≠ 0 → ∫ t : T, w ((t : G) * x) ∂τ = 1) :
    ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) ∂μ < ∞ := by
  have := sFinite_subgroup_haar T τ hT
  obtain ⟨U, hUo, hCU, hUc⟩ := exists_isOpen_superset_and_isCompact_closure hwc.isCompact
  obtain ⟨V₀, hV₀, hV₀U⟩ := compact_open_separated_mul_left hwc.isCompact hUo hCU
  obtain ⟨V, hVV₀, hVo, h1V⟩ := mem_nhds_iff.1 hV₀
  set m : ℝ≥0∞ := min (τ ((Subtype.val : T → G) ⁻¹' V)) 1 with hm
  have hm_pos : m ≠ 0 := by
    have h1 : τ ((Subtype.val : T → G) ⁻¹' V) ≠ 0 :=
      ((hVo.preimage continuous_subtype_val).measure_pos τ ⟨⟨1, T.one_mem⟩, h1V⟩).ne'
    simp [hm, h1]
  have hm_top : m ≠ ∞ := by simp [hm]
  let Φ₀ : G → ℝ≥0∞ := fun x => ∫⁻ t : T, U.indicator 1 ((t : G) * x) ∂τ
  have hΦ₀ : ∀ x ∈ tsupport w, m ≤ Φ₀ x := by
    intro x hx
    have hsub : (Subtype.val : T → G) ⁻¹' V ⊆
        (fun t : T => (t : G) * x) ⁻¹' U := by
      intro t ht
      exact hV₀U (Set.mul_mem_mul (hVV₀ ht) hx)
    calc m ≤ τ ((Subtype.val : T → G) ⁻¹' V) := min_le_left _ _
      _ ≤ τ ((fun t : T => (t : G) * x) ⁻¹' U) := measure_mono hsub
      _ = Φ₀ x := by
        have hUx : MeasurableSet ((fun t : T => (t : G) * x) ⁻¹' U) :=
          measurableSet_preimage (continuous_subtype_val.mul continuous_const).measurable
            hUo.measurableSet
        simp only [Φ₀]
        rw [← lintegral_indicator_one hUx]
        rfl
  have hUind : Measurable (U.indicator (1 : G → ℝ≥0∞)) :=
    measurable_one.indicator hUo.measurableSet
  have hint2 : Measurable fun p : G × T =>
      ‖F p.1‖ₑ * ENNReal.ofReal (w p.1) * U.indicator 1 ((p.2 : G) * p.1) :=
    ((hFm.comp measurable_fst).enorm.mul
      (ENNReal.measurable_ofReal.comp (hwm.comp measurable_fst))).mul
      (hUind.comp (measurable_subgroup_mul T))
  have step1 : ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) ∂μ ≤
      m⁻¹ * ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) * Φ₀ x ∂μ := by
    rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hm_pos)]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ tsupport w
    · have h1 : (1 : ℝ≥0∞) ≤ m⁻¹ * Φ₀ x := by
        calc (1 : ℝ≥0∞) = m⁻¹ * m := (ENNReal.inv_mul_cancel hm_pos hm_top).symm
          _ ≤ m⁻¹ * Φ₀ x := mul_le_mul_right (hΦ₀ x hx) _
      calc ‖F x‖ₑ * ENNReal.ofReal (w x) =
            ‖F x‖ₑ * ENNReal.ofReal (w x) * 1 := (mul_one _).symm
        _ ≤ ‖F x‖ₑ * ENNReal.ofReal (w x) * (m⁻¹ * Φ₀ x) := mul_le_mul_right h1 _
        _ = m⁻¹ * (‖F x‖ₑ * ENNReal.ofReal (w x) * Φ₀ x) := by ring
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  have step2 : ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) * Φ₀ x ∂μ =
      ∫⁻ x, ‖F x‖ₑ * U.indicator 1 x *
        ∫⁻ t : T, ENNReal.ofReal (w ((t : G) * x)) ∂τ ∂μ := by
    calc ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) * Φ₀ x ∂μ
        = ∫⁻ x, ∫⁻ t : T, ‖F x‖ₑ * ENNReal.ofReal (w x) *
            U.indicator 1 ((t : G) * x) ∂τ ∂μ := by
          refine lintegral_congr fun x => ?_
          rw [lintegral_const_mul' _ _
            (ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top)]
      _ = ∫⁻ t : T, ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) *
            U.indicator 1 ((t : G) * x) ∂μ ∂τ :=
          lintegral_lintegral_swap hint2.aemeasurable
      _ = ∫⁻ t : T, ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w ((t : G)⁻¹ * x)) *
            U.indicator 1 x ∂μ ∂τ := by
          refine lintegral_congr fun t => ?_
          have h := lintegral_mul_left_eq_self (μ := μ)
            (fun x => ‖F ((t : G)⁻¹ * x)‖ₑ * ENNReal.ofReal (w ((t : G)⁻¹ * x)) *
              U.indicator 1 x) (t : G)
          simp only [inv_mul_cancel_left] at h
          rw [h]
          refine lintegral_congr fun x => ?_
          have hF : F ((t : G)⁻¹ * x) = F x := by simpa using hFT t⁻¹ x
          rw [hF]
      _ = ∫⁻ t : T, ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w ((t : G) * x)) *
            U.indicator 1 x ∂μ ∂τ := by
          rw [← lintegral_inv_eq_self]
          simp
      _ = ∫⁻ x, ∫⁻ t : T, ‖F x‖ₑ * ENNReal.ofReal (w ((t : G) * x)) *
            U.indicator 1 x ∂τ ∂μ := by
          refine (lintegral_lintegral_swap ?_).symm
          exact (((hFm.comp measurable_fst).enorm.mul
            (ENNReal.measurable_ofReal.comp (hwm.comp (measurable_subgroup_mul T)))).mul
            (hUind.comp measurable_fst)).aemeasurable
      _ = ∫⁻ x, ‖F x‖ₑ * U.indicator 1 x *
            ∫⁻ t : T, ENNReal.ofReal (w ((t : G) * x)) ∂τ ∂μ := by
          refine lintegral_congr fun x => ?_
          rw [← lintegral_const_mul' _ _
            (ENNReal.mul_ne_top enorm_ne_top (by by_cases hxU : x ∈ U <;> simp [hxU]))]
          refine lintegral_congr fun t => ?_
          ring
  have step3 : ∫⁻ x, ‖F x‖ₑ * U.indicator 1 x *
        ∫⁻ t : T, ENNReal.ofReal (w ((t : G) * x)) ∂τ ∂μ ≤
      ∫⁻ x, U.indicator (fun _ => (‖C‖₊ : ℝ≥0∞)) x ∂μ := by
    refine lintegral_mono fun x => ?_
    by_cases hF : F x = 0
    · simp [hF]
    · rw [lintegral_fibre_eq_one T τ hw0 hwm (hw1 x hF), mul_one]
      by_cases hxU : x ∈ U
      · rw [Set.indicator_of_mem hxU, Set.indicator_of_mem hxU, Pi.one_apply, mul_one]
        have h : ‖F x‖₊ ≤ ‖C‖₊ := by
          rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
          exact (hFb x).trans (Real.le_norm_self C)
        exact enorm_le_coe.2 h
      · simp [hxU]
  have step4 : ∫⁻ x, U.indicator (fun _ => (‖C‖₊ : ℝ≥0∞)) x ∂μ < ∞ := by
    rw [lintegral_indicator_const hUo.measurableSet]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top
      ((measure_mono subset_closure).trans_lt hUc.measure_lt_top)
  calc ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) ∂μ
      ≤ m⁻¹ * ∫⁻ x, ‖F x‖ₑ * ENNReal.ofReal (w x) * Φ₀ x ∂μ := step1
    _ ≤ m⁻¹ * ∫⁻ x, U.indicator (fun _ => (‖C‖₊ : ℝ≥0∞)) x ∂μ := by
        rw [step2]
        exact mul_le_mul_right step3 _
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hm_pos)) step4

/-- A bounded measurable `T`-invariant complex function is integrable against
any nonnegative measurable compactly supported weight whose `T`-average is
one wherever the function is nonzero. The weight need not be bounded. -/
theorem integrable_mul_of_integral_subgroup_translate_eq_one
    (F : G → ℂ) (hFm : Measurable F) (hFb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C)
    (hFT : ∀ (t : T) (x : G), F ((t : G) * x) = F x)
    (w : G → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hwm : Measurable w)
    (hwc : HasCompactSupport w)
    (hw1 : ∀ x, F x ≠ 0 → ∫ t : T, w ((t : G) * x) ∂τ = 1) :
    Integrable (fun x => F x * (w x : ℂ)) μ := by
  obtain ⟨C, hC⟩ := hFb
  refine ⟨(hFm.mul (Complex.measurable_ofReal.comp hwm)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa only [enorm_mul, enorm_ofReal_of_nonneg (hw0 _)] using
    lintegral_enorm_mul_lt_top T μ τ hT F hFm hC hFT w hw0 hwm hwc hw1

end

/-- The integral of a bounded measurable `T`-invariant complex function
against a nonnegative measurable compactly supported cutoff does not depend
on the cutoff, when each cutoff has subgroup integral one on the support of
that function. Normalization is not required outside its support.

The more general `integral_mul_eq_of_normalized_subgroup` does not require
boundedness or compact support; the hypotheses here also guarantee
integrability by `integrable_mul_of_integral_subgroup_translate_eq_one`. -/
theorem integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (μ : Measure G) [μ.IsHaarMeasure] (τ : Measure T) [τ.IsHaarMeasure] [τ.IsInvInvariant]
    (F : G → ℂ) (hFm : Measurable F) (hFb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C)
    (hFT : ∀ (t : T) (x : G), F ((t : G) * x) = F x)
    (w₁ w₂ : G → ℝ)
    (hw₁ : (∀ x, 0 ≤ w₁ x) ∧ Measurable w₁ ∧ HasCompactSupport w₁ ∧
      ∀ x, F x ≠ 0 → ∫ t : T, w₁ ((t : G) * x) ∂τ = 1)
    (hw₂ : (∀ x, 0 ≤ w₂ x) ∧ Measurable w₂ ∧ HasCompactSupport w₂ ∧
      ∀ x, F x ≠ 0 → ∫ t : T, w₂ ((t : G) * x) ∂τ = 1) :
    ∫ x, F x * (w₁ x : ℂ) ∂μ = ∫ x, F x * (w₂ x : ℂ) ∂μ := by
  rcases hFb with ⟨_, _⟩
  have := sFinite_subgroup_haar T τ hT
  exact integral_mul_eq_of_normalized_subgroup μ T continuous_subtype_val.measurable
    τ F hFm hFT w₁ w₂ hw₁.1 hw₂.1 hw₁.2.1 hw₂.2.1 hw₁.2.2.2 hw₂.2.2.2

end MeasureTheory

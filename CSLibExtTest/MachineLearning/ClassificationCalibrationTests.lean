/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.ClassificationCalibration
public import CSLibExt.MachineLearning.Classification.LogisticSVM
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Tactic.NormNum

/-!
# Classification-calibration tests

The exponential loss `exp (-α)` of AdaBoost and the hinge loss `max 0 (1 - α)` of support
vector machines are convex, nonnegative and have slope `-1` at `0`, so both are
classification-calibrated (Bartlett, Jordan and McAuliffe, Examples 1 and 4). The conditional
risk is reflected by `η ↦ 1 - η`.

The characterization `isClassificationCalibrated_iff_differentiableAt_and_deriv_neg` shows that
the logistic loss is classification-calibrated and that `α ^ 2` (slope `0` at `0`) and
`max 0 (-α)` (not differentiable at `0`) are not. Two witnesses show that its hypotheses are
needed: the convex loss `-α` with slope `-1` at `0` is not classification-calibrated, since `H`
and `H⁻` are infima in `ℝ` and nonnegativity keeps them genuine, and the nonconvex 0-1 loss is
classification-calibrated but not differentiable at `0`.
-/

namespace Cslib.MachineLearning.ClassificationCalibration

open Real

example (η α : ℝ) : condRisk (fun x => exp (-x)) η α =
    η * exp (-α) + (1 - η) * exp α := by
  simp [condRisk]

/-- The exponential loss is classification-calibrated. -/
example : IsClassificationCalibrated fun x => exp (-x) := by
  refine isClassificationCalibrated_of_hasDerivAt (d := -1) (fun x => (exp_pos _).le) ?_ ?_
    (by norm_num)
  · simpa [Function.comp_def] using
      convexOn_exp.comp_linearMap (-LinearMap.id : ℝ →ₗ[ℝ] ℝ)
  · have := (hasDerivAt_neg (0 : ℝ)).exp
    simpa using this

/-- The hinge loss is classification-calibrated. -/
example : IsClassificationCalibrated fun x => max 0 (1 - x) := by
  refine isClassificationCalibrated_of_hasDerivAt (d := -1) (fun x => le_max_left _ _) ?_ ?_
    (by norm_num)
  · have hlin : ConvexOn ℝ Set.univ fun x : ℝ => 1 - x := by
      have := ((-LinearMap.id : ℝ →ₗ[ℝ] ℝ).convexOn convex_univ).add_const 1
      exact this.congr fun x _ => by simp; ring
    exact (convexOn_const 0 convex_univ).sup hlin
  · have h : HasDerivAt (fun x : ℝ => 1 - x) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_sub 1
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact max_eq_right (by simp at hx; linarith)

/-- The logistic loss `log (1 + exp (-α))` is nonnegative and convex with slope `-1/2` at `0`,
so it is classification-calibrated. -/
example : IsClassificationCalibrated fun x => Real.log (1 + exp (-x)) := by
  have hd : HasDerivAt (fun x => Real.log (1 + exp (-x))) (-2⁻¹) 0 := by
    simpa [Function.comp_def] using
      (LogisticSVM.hasDerivAt_log_one_add_exp (-0)).comp 0 (hasDerivAt_neg 0)
  refine (isClassificationCalibrated_iff_differentiableAt_and_deriv_neg (fun x => ?_) ?_).2
    ⟨hd.differentiableAt, by rw [hd.deriv]; norm_num⟩
  · exact Real.log_nonneg (by linarith [exp_pos (-x)])
  · simpa [Function.comp_def] using
      LogisticSVM.convexOn_log_one_add_exp.comp_linearMap (-LinearMap.id : ℝ →ₗ[ℝ] ℝ)

/-- The square `α ^ 2` is nonnegative and convex with slope `0` at `0`, so it is not
classification-calibrated. -/
example : ¬IsClassificationCalibrated fun x : ℝ => x ^ 2 := by
  intro h
  have := (differentiableAt_and_deriv_neg_of_isClassificationCalibrated
    (even_two.convexOn_pow (𝕜 := ℝ)) h).2
  simp at this

/-- The loss `max 0 (-α)` is nonnegative and convex but not differentiable at `0`, so it is not
classification-calibrated (Bach, *Learning Theory from First Principles*, Section 4.1.3, after
Proposition 4.1). -/
example : ¬IsClassificationCalibrated fun x : ℝ => max 0 (-x) := by
  intro h
  have hconv : ConvexOn ℝ Set.univ fun x : ℝ => max 0 (-x) :=
    (convexOn_const 0 convex_univ).sup ((-LinearMap.id : ℝ →ₗ[ℝ] ℝ).convexOn convex_univ)
  have hd := (differentiableAt_and_deriv_neg_of_isClassificationCalibrated hconv h).1
  have habs : (abs : ℝ → ℝ) = fun x => 2 * max 0 (-x) + x := by
    funext x
    rcases le_total 0 x with hx | hx
    · simp [abs_of_nonneg hx, hx]
    · rw [abs_of_nonpos hx, max_eq_right (neg_nonneg.2 hx)]; ring
  exact not_differentiableAt_abs_zero (habs ▸ (hd.const_mul 2).add differentiableAt_id)

/-- Nonnegativity cannot be dropped from the characterization as `H` and `H⁻` are defined here,
as infima in `ℝ`: the loss `-α` is convex and differentiable at `0` with slope `-1`, but
`C_1(α) = -α` is unbounded below, so `H(1)` is the value `0` that `ℝ` gives an infimum unbounded
below, which equals `H⁻(1) = C_1(0) = 0`. -/
example : ConvexOn ℝ Set.univ (fun x : ℝ => -x) ∧ DifferentiableAt ℝ (fun x : ℝ => -x) 0 ∧
    deriv (fun x : ℝ => -x) 0 < 0 ∧ ¬IsClassificationCalibrated fun x : ℝ => -x := by
  refine ⟨(concaveOn_id convex_univ).neg, differentiableAt_id.neg, by simp, fun h => ?_⟩
  have h1 := h 1 ⟨zero_le_one, le_rfl⟩ (by norm_num)
  have hH : optRisk (fun x : ℝ => -x) 1 = 0 := by
    refine Real.iInf_of_not_bddBelow fun ⟨m, hm⟩ => ?_
    have := hm ⟨-m + 1, rfl⟩
    norm_num [condRisk] at this
  have hW : wrongSignRisk (fun x : ℝ => -x) 1 ≤ 0 := by
    refine ciInf_le_of_le ⟨0, ?_⟩ ⟨0, by norm_num⟩ (by simp [condRisk])
    rintro _ ⟨⟨α, hα⟩, rfl⟩
    simp only [condRisk]
    norm_num at hα ⊢
    linarith
  linarith

/-- Convexity cannot be dropped from the necessity direction: the 0-1 loss `𝟙[α ≤ 0]` is
classification-calibrated, as `H(η) = min(η, 1 - η) < max(η, 1 - η) = H⁻(η)` for `η ≠ 1/2`,
but it is not continuous at `0`, so not differentiable there. -/
example : IsClassificationCalibrated (fun x : ℝ => if x ≤ 0 then (1 : ℝ) else 0) ∧
    ¬DifferentiableAt ℝ (fun x : ℝ => if x ≤ 0 then (1 : ℝ) else 0) 0 := by
  set φ : ℝ → ℝ := fun x => if x ≤ 0 then (1 : ℝ) else 0 with hφ
  have key : ∀ η : ℝ, 1 / 2 < η → η ≤ 1 → optRisk φ η < wrongSignRisk φ η := by
    intro η hη hη1
    have hbdd : BddBelow (Set.range (condRisk φ η)) := ⟨0, by
      rintro _ ⟨α, rfl⟩
      exact condRisk_nonneg (fun x => by simp only [hφ]; split_ifs <;> norm_num)
        ⟨by linarith, hη1⟩ α⟩
    have hH : optRisk φ η ≤ 1 - η := ciInf_le_of_le hbdd 1 (by norm_num [condRisk, hφ])
    have hW : η ≤ wrongSignRisk φ η := by
      have : Nonempty {α : ℝ // α * (2 * η - 1) ≤ 0} := ⟨⟨0, by simp⟩⟩
      refine le_ciInf fun ⟨α, hα⟩ => ?_
      have hα0 : α ≤ 0 := by nlinarith
      simp only [condRisk, hφ, hα0, ↓reduceIte]
      split_ifs <;> linarith
    linarith
  refine ⟨fun η hη hne => ?_, fun hd => ?_⟩
  · rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h := key (1 - η) (by linarith) (by linarith [hη.1])
      rwa [optRisk_one_sub, wrongSignRisk_one_sub] at h
    · exact key η hgt hη.2
  · have h1 : Filter.Tendsto φ (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ 0)) :=
      hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Filter.Tendsto φ (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun x (hx : 0 < x) => by
        simp [hφ, not_le.2 hx])
    have := tendsto_nhds_unique h1 h2
    simp [hφ] at this

end Cslib.MachineLearning.ClassificationCalibration

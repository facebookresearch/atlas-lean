/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Normed.Module.AsymptoticModuli
import Mathlib.Tactic.NormNum

/-! # Tests for unit-direction asymptotic moduli -/

open MetaMathlibExt
open scoped NNReal

-- The ambient norm supplies a unit direction in every admissible subspace in infinite dimension.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : ¬ FiniteDimensional ℝ E) (F : ClosedFiniteCodimensionalSubmodule E) :
    ∃ y ∈ F.val, ‖y‖ = 1 := by
  simpa only [coe_normSeminorm] using
    F.exists_seminorm_eq_one (normSeminorm ℝ E) hE (α := 1) zero_lt_one (by simp)

-- There are no centers for the zero seminorm, even though the ambient space is nontrivial.
example (t : ℝ) : asymptoticConvexityModulus (0 : Seminorm ℝ ℝ) t = 0 := by
  have : IsEmpty {x : ℝ // (0 : Seminorm ℝ ℝ) x = 1} :=
    ⟨fun x ↦ zero_ne_one (by simpa only [zero_apply] using x.property)⟩
  exact Real.iInf_of_isEmpty _

-- A rescaled norm has a unit vector of ambient norm 1/2, not 1.
example :
    let N : Seminorm ℝ ℝ := (2 : ℝ≥0) • normSeminorm ℝ ℝ
    N (1 / 2) = 1 ∧ asymptoticConvexityModulus N 0 = 0 ∧ asymptoticMidpointModulus N 0 = 0 := by
  dsimp only
  refine ⟨?_, asymptoticConvexityModulus_zero _, asymptoticMidpointModulus_zero _⟩
  norm_num [smul_apply, NNReal.smul_def, coe_normSeminorm, Real.norm_eq_abs]

private theorem eq_one_or_neg_one {x : ℝ} (hx : ‖x‖ = 1) : x = 1 ∨ x = -1 := by
  rw [Real.norm_eq_abs] at hx
  by_cases h : 0 ≤ x
  · exact Or.inl ((abs_of_nonneg h).symm.trans hx)
  · exact Or.inr (neg_eq_iff_eq_neg.mp ((abs_of_neg (lt_of_not_ge h)).symm.trans hx))

-- The average of the two norms on the real unit sphere at step 2 is 2;
-- their maximum would be 3. Empty direction sets cannot increase the supremum.
example : asymptoticMidpointModulus (normSeminorm ℝ ℝ) 2 = 1 := by
  let X := {x : ℝ // ‖x‖ = 1}
  let D (F : ClosedFiniteCodimensionalSubmodule ℝ) := {y : ℝ // y ∈ F.val ∧ ‖y‖ = 1}
  let F₀ : ClosedFiniteCodimensionalSubmodule ℝ := ⟨⊤, by simp, by infer_instance⟩
  have : Nonempty X := ⟨⟨1, norm_one⟩⟩
  have : Nonempty (D F₀) := ⟨⟨1, Submodule.mem_top, norm_one⟩⟩
  let f (x : X) (F : ClosedFiniteCodimensionalSubmodule ℝ) : ℝ :=
    ⨅ y : D F, (‖x.val + (2 : ℝ) • y.val‖ + ‖x.val - (2 : ℝ) • y.val‖) / 2 - 1
  have hf (x : X) (F : ClosedFiniteCodimensionalSubmodule ℝ) :
      f x F = ⨅ _ : D F, (1 : ℝ) := by
    unfold f
    apply congrArg iInf
    funext y
    obtain hx | hx := eq_one_or_neg_one x.property <;>
      obtain hy | hy := eq_one_or_neg_one y.property.2 <;>
      norm_num [hx, hy, smul_eq_mul, Real.norm_eq_abs]
  have hsup (x : X) : (⨆ F, f x F) = 1 := by
    have hle (F : ClosedFiniteCodimensionalSubmodule ℝ) : f x F ≤ 1 := by
      rw [hf]
      cases isEmpty_or_nonempty (D F)
      · rw [Real.iInf_of_isEmpty]
        exact zero_le_one
      · rw [ciInf_const]
    have : Nonempty (ClosedFiniteCodimensionalSubmodule ℝ) := ⟨F₀⟩
    refine le_antisymm (ciSup_le hle) ?_
    calc (1 : ℝ) = f x F₀ := by rw [hf, ciInf_const]
      _ ≤ ⨆ F, f x F := le_ciSup ⟨1, by rintro _ ⟨F, rfl⟩; exact hle F⟩ F₀
  change (⨅ x : X, ⨆ F, f x F) = 1
  simp only [hsup, ciInf_const]

-- Unit directions for the doubled norm are ±1/2, not ±1.
-- Using the ambient-unit directions would give a modulus of 3 instead of 1.
example : asymptoticMidpointModulus ((2 : ℝ≥0) • normSeminorm ℝ ℝ) 2 = 1 := by
  let N : Seminorm ℝ ℝ := (2 : ℝ≥0) • normSeminorm ℝ ℝ
  let X := {x : ℝ // N x = 1}
  let D (F : ClosedFiniteCodimensionalSubmodule ℝ) := {y : ℝ // y ∈ F.val ∧ N y = 1}
  let F₀ : ClosedFiniteCodimensionalSubmodule ℝ := ⟨⊤, by simp, by infer_instance⟩
  have hn (z : ℝ) : N z = 2 * |z| := by
    norm_num [N, smul_apply, NNReal.smul_def, coe_normSeminorm, Real.norm_eq_abs]
  have hhalf : N (1 / 2) = 1 := by norm_num [hn]
  have : Nonempty X := ⟨⟨1 / 2, hhalf⟩⟩
  have : Nonempty (D F₀) := ⟨⟨1 / 2, Submodule.mem_top, hhalf⟩⟩
  have hunit {z : ℝ} (hz : N z = 1) : z = 1 / 2 ∨ z = -(1 / 2) := by
    have habs : |z| = 1 / 2 := (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2 <| by
      rwa [hn, mul_comm] at hz
    by_cases h : 0 ≤ z
    · exact Or.inl (by simpa only [abs_of_nonneg h] using habs)
    · exact Or.inr (neg_eq_iff_eq_neg.mp (by simpa only [abs_of_neg (lt_of_not_ge h)] using habs))
  have hpoint (x : X) {F : ClosedFiniteCodimensionalSubmodule ℝ} (y : D F) :
      (N (x.val + (2 : ℝ) • y.val) + N (x.val - (2 : ℝ) • y.val)) / 2 - 1 = 1 := by
    obtain hx | hx := hunit x.property <;> obtain hy | hy := hunit y.property.2 <;>
      norm_num [hn, hx, hy, smul_eq_mul]
  have hsup : (⨆ F, ⨅ _ : D F, (1 : ℝ)) = 1 := by
    have hle (F : ClosedFiniteCodimensionalSubmodule ℝ) : (⨅ _ : D F, (1 : ℝ)) ≤ 1 := by
      cases isEmpty_or_nonempty (D F)
      · rw [Real.iInf_of_isEmpty]
        exact zero_le_one
      · rw [ciInf_const]
    have : Nonempty (ClosedFiniteCodimensionalSubmodule ℝ) := ⟨F₀⟩
    refine le_antisymm (ciSup_le hle) ?_
    calc (1 : ℝ) = ⨅ _ : D F₀, (1 : ℝ) := ciInf_const.symm
      _ ≤ ⨆ F, ⨅ _ : D F, (1 : ℝ) :=
        le_ciSup (f := fun F ↦ ⨅ _ : D F, (1 : ℝ)) ⟨1, by rintro _ ⟨F, rfl⟩; exact hle F⟩ F₀
  change (⨅ x : X, ⨆ F, ⨅ y : D F,
    (N (x.val + (2 : ℝ) • y.val) + N (x.val - (2 : ℝ) • y.val)) / 2 - 1) = 1
  simp only [hpoint, hsup, ciInf_const]

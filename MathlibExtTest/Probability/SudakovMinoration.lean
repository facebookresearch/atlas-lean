/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.SudakovMinoration

/-!
# Tests for Sudakov minoration

A singleton permits arbitrary separation. The process with coordinates zero and a standard
normal has canonical separation one and its maximum is the positive part of the normal.
-/

open MeasureTheory ProbabilityTheory MathlibExt.Probability.GenericChaining
open MathlibExt.Probability.MajorizingMeasureWanted

example : ∃ L : ℝ, 0 < L ∧ ∀ a : ℝ, 0 ≤ a →
    a / L * Real.sqrt (Real.log (Fintype.card Unit)) ≤ ∫ x, ⨆ _ : Unit, x ∂gaussianReal 0 1 := by
  obtain ⟨L, hL, h⟩ := sudakov_minoration
  refine ⟨L, hL, fun a ha => ?_⟩
  let A : ℝ →L[ℝ] (Unit → ℝ) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ ℝ
  have hG := isGaussian_map (μ := gaussianReal 0 1) A
  exact h ℝ (gaussianReal 0 1) Unit (fun _ x => x) a
    (fun _ => measurable_id) hG (fun _ => integral_id_gaussianReal) ha
    (fun _ _ hne => (hne (Subsingleton.elim _ _)).elim)

example : 0 < ∫ x, max x 0 ∂gaussianReal 0 1 := by
  let P := gaussianReal 0 1
  let A : ℝ →L[ℝ] (Bool → ℝ) := ContinuousLinearMap.pi fun i =>
    if i then ContinuousLinearMap.id ℝ ℝ else 0
  let X := fun i (x : ℝ) => A x i
  have hX (i : Bool) : Measurable (X i) := (measurable_pi_apply i).comp A.continuous.measurable
  have hG : IsGaussian (P.map fun x i => X i x) := isGaussian_map A
  have hcen (i : Bool) : ∫ x, X i x ∂P = 0 := by
    cases i <;> simp [X, A, P, integral_id_gaussianReal]
  have hsq : ∫ x, x ^ 2 ∂P = 1 := by
    have hv := variance_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_eq_integral aemeasurable_id] at hv
    simpa [P, integral_id_gaussianReal] using hv
  have hsep (i j : Bool) (hne : i ≠ j) : ENNReal.ofReal 1 ≤ canonicalDist P X i j := by
    rw [canonicalDist_eq_ofReal_sqrt (memLp_sub_of_isGaussian P X hX hG i j)]
    cases i <;> cases j <;> simp_all [X, A]
  have hmax (x : ℝ) : (⨆ i, X i x) = max x 0 := by
    apply le_antisymm
    · apply ciSup_le
      rintro (_ | _) <;> simp [X, A]
    · exact max_le (le_ciSup (Set.finite_range (X · x)).bddAbove true)
        (le_ciSup (Set.finite_range (X · x)).bddAbove false)
  obtain ⟨L, hL, h⟩ := sudakov_minoration
  have hb := h ℝ P Bool X 1 hX hG hcen zero_le_one hsep
  simp only [Fintype.card_bool, Nat.cast_ofNat, hmax] at hb
  exact lt_of_lt_of_le
    (mul_pos (div_pos one_pos hL) (Real.sqrt_pos.mpr (Real.log_pos (by norm_num)))) hb

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Nonparametric.EmpiricalCDFPointwise

@[expose] public section

open Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

lemma empCDF_nonneg {n : ℕ} (X : Fin n → ℝ) (t : ℝ) : 0 ≤ empCDF X t := by
  unfold empCDF
  positivity

lemma empCDF_le_one {n : ℕ} (hn : 0 < n) (X : Fin n → ℝ) (t : ℝ) :
    empCDF X t ≤ 1 := by
  unfold empCDF
  rw [div_le_one (Nat.cast_pos.mpr hn)]
  calc ((Finset.univ.filter (fun i => X i ≤ t)).card : ℝ)
      ≤ ((Finset.univ : Finset (Fin n)).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_filter_le _ _)
    _ = (n : ℝ) := by rw [Finset.card_univ, Fintype.card_fin]

/-- Positive case: with one observation the empirical CDF is the indicator. -/
example {Ω : Type*} [MeasurableSpace Ω]
    (X : Fin 1 → Ω → ℝ) (ω : Ω) (x : ℝ) :
    empCDF (fun i => X i ω) x = (if X ⟨0, by omega⟩ ω ≤ x then 1 else 0) := by
  unfold empCDF
  have h1 : ∀ i : Fin 1, i = ⟨0, by omega⟩ := fun i => Fin.ext (Nat.lt_one_iff.mp i.2)
  split_ifs with h
  · have hfil : Finset.univ.filter (fun i : Fin 1 => X i ω ≤ x) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro i _
      rw [h1 i]
      exact h
    rw [hfil, Finset.card_univ, Fintype.card_fin]
    norm_num
  · have hfil : Finset.univ.filter (fun i : Fin 1 => X i ω ≤ x) = ∅ := by
      apply Finset.filter_false_of_mem
      intro i _
      rw [h1 i]
      exact h
    rw [hfil, Finset.card_empty]
    norm_num

set_option linter.unusedVariables false in
/-- Boundary case: `eps = 1` is vacuous for a `[0, 1]`-valued deviation. The
deviation never exceeds one, so the bad event is empty. -/
example {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Fin n → Ω → ℝ) (ω : Ω) (x : ℝ)
    (F : ℝ → ℝ) (hF : ∀ y, 0 ≤ F y ∧ F y ≤ 1) :
    {ω | (1 : ℝ) < |empCDF (fun i => X i ω) x - F x|} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro ω h
  simp only [Set.mem_ofPred_eq] at h
  have hE0 : 0 ≤ empCDF (fun i => X i ω) x := empCDF_nonneg _ _
  have hE1 : empCDF (fun i => X i ω) x ≤ 1 := empCDF_le_one hn _ _
  obtain ⟨hF0, hF1⟩ := hF x
  rw [lt_abs] at h
  rcases h with h | h <;> linarith

/-- Non-vacuity: at `n = 10` observations and `eps = 1 / 2` the bound is
strictly below one. -/
example : (2 : ℝ) * Real.exp (-2 * 10 * (1 / 2 : ℝ) ^ 2) < 1 := by
  have harg : (-2 * 10 * (1 / 2 : ℝ) ^ 2) = -(5 : ℝ) := by norm_num
  rw [harg, Real.exp_neg]
  have h5 : (5 : ℝ) + 1 ≤ Real.exp 5 := Real.add_one_le_exp 5
  have hpos : (0 : ℝ) < Real.exp 5 := Real.exp_pos 5
  rw [← div_eq_mul_inv, div_lt_one hpos]
  linarith

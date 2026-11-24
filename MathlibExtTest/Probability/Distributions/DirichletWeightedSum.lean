/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.DirichletWeightedSum

@[expose] public section

/-!
# Tests for the distribution function of a weighted sum of a flat Dirichlet vector
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MathlibExtTest.Probability.Distributions.DirichletWeightedSum

private lemma erase_zero_two : (Finset.univ : Finset (Fin (1 + 1))).erase 0 = {1} := by decide
private lemma erase_one_two : (Finset.univ : Finset (Fin (1 + 1))).erase 1 = {0} := by decide
private lemma erase_zero_three : (Finset.univ : Finset (Fin (2 + 1))).erase 0 = {1, 2} := by
  decide
private lemma erase_one_three : (Finset.univ : Finset (Fin (2 + 1))).erase 1 = {0, 2} := by
  decide
private lemma erase_two_three : (Finset.univ : Finset (Fin (2 + 1))).erase 2 = {0, 1} := by
  decide

private lemma injective_two {a b : ℝ} (h : a ≠ b) : Function.Injective ![a, b] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- Signed, unsorted weights in two coordinates: `2θ₀ - θ₁ ≤ 0` iff `θ₀ ≤ 1/3`. -/
example : (dirichletMeasure (fun _ : Fin 2 ↦ (1 : ℝ))).real
    {θ | ∑ j, ![2, -1] j * θ j ≤ 0} = 1 / 3 := by
  rw [dirichletMeasure_one_real_weightedSum_le le_rfl (injective_two (by norm_num))]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, erase_zero_two,
    erase_one_two, Finset.prod_singleton]
  norm_num

/-- The level `x` may equal a weight: at the largest weight the probability is `1`. -/
example : (dirichletMeasure (fun _ : Fin 2 ↦ (1 : ℝ))).real
    {θ | ∑ j, ![2, -1] j * θ j ≤ 2} = 1 := by
  rw [dirichletMeasure_one_real_weightedSum_le le_rfl (injective_two (by norm_num))]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, erase_zero_two,
    erase_one_two, Finset.prod_singleton]
  norm_num

/-- At the smallest weight the probability is `0`. -/
example : (dirichletMeasure (fun _ : Fin 2 ↦ (1 : ℝ))).real
    {θ | ∑ j, ![2, -1] j * θ j ≤ -1} = 0 := by
  rw [dirichletMeasure_one_real_weightedSum_le le_rfl (injective_two (by norm_num))]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, erase_zero_two,
    erase_one_two, Finset.prod_singleton]
  norm_num

/-- Below every weight the probability is `0`. -/
example : (dirichletMeasure (fun _ : Fin 2 ↦ (1 : ℝ))).real
    {θ | ∑ j, ![-1, 1] j * θ j ≤ -2} = 0 := by
  rw [dirichletMeasure_one_real_weightedSum_le le_rfl (injective_two (by norm_num))]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, erase_zero_two,
    erase_one_two, Finset.prod_singleton]
  norm_num

/-- Three coordinates with unsorted weights `(0, 3, 1)` at the interior level `2`: the full sum
gives `4/3 + 0 - 1/2 = 5/6`. -/
example : (dirichletMeasure (fun _ : Fin 3 ↦ (1 : ℝ))).real
    {θ | ∑ j, ![0, 3, 1] j * θ j ≤ 2} = 5 / 6 := by
  have hw : Function.Injective (![0, 3, 1] : Fin 3 → ℝ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | norm_num at hij
  rw [dirichletMeasure_one_real_weightedSum_le (by norm_num) hw]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    erase_zero_three, erase_one_three, erase_two_three]
  norm_num

/-- Above every weight the formula saturates at `1`, by the saturation identity. -/
example {n : ℕ} (hn : 1 ≤ n) {w : Fin (n + 1) → ℝ} (hw : Function.Injective w) {x : ℝ}
    (hx : ∀ j, w j ≤ x) :
    (dirichletMeasure (fun _ ↦ (1 : ℝ))).real {θ | ∑ j, w j * θ j ≤ x} = 1 := by
  rw [dirichletMeasure_one_real_weightedSum_le hn hw]
  have h : ∀ j, max (x - w j) 0 = x - w j := fun j ↦ max_eq_left (sub_nonneg.2 (hx j))
  simp_rw [h]
  rw [sum_sub_pow_div_prod_erase_sub hw, ← mul_pow]
  norm_num

/-- Lagrange interpolation of `1` on the nodes `0, 1, 3`. -/
example : ∑ i, 1 / ∏ m ∈ Finset.univ.erase i, ((![0, 1, 3] : Fin 3 → ℝ) i - ![0, 1, 3] m) =
    0 := by
  simp only [Fin.sum_univ_three, erase_zero_three, erase_one_three, erase_two_three]
  norm_num

/-- Why `1 ≤ n` is assumed: with one coordinate the right-hand side is `1` at every level
(`0 ^ 0 = 1`), while the event `w₀ θ₀ ≤ x` has probability `0` for `x < w₀`. -/
example (w : Fin 1 → ℝ) (x : ℝ) :
    (-1) ^ 0 * ∑ j, (max (x - w j) 0) ^ 0 / ∏ m ∈ Finset.univ.erase j, (w j - w m) = 1 := by
  simp

end MathlibExtTest.Probability.Distributions.DirichletWeightedSum

#print axioms dirichletMeasure_one_real_weightedSum_le
#print axioms sum_inv_prod_erase_sub_eq_zero
#print axioms sum_sub_pow_div_prod_erase_sub

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.MvPolynomial.BernsteinConvergence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open MvPolynomial

-- The uniform interface accepts independently chosen coordinate degrees.
example (p : MvPolynomial (Fin 2) ℝ) (N : ℕ) (hN : 0 < N)
    (hp : ∀ i, 2 * p.degreeOf i ≤ N) (k : Fin 2 → ℕ)
    (hk : ∀ i, k i ≤ ![N + 3, N + 7] i) :
    |bernsteinCoeff ![N + 3, N + 7] p k -
      eval (fun i => (k i : ℝ) / ((![N + 3, N + 7] : Fin 2 → ℕ) i : ℝ)) p| ≤ bernsteinErrorConstant p / N := by
  apply abs_bernsteinCoeff_sub_eval_le hN hp
  · intro i
    fin_cases i <;> simp
  · exact hk

private noncomputable def quadratic : MvPolynomial (Fin 1) ℝ :=
  monomial (Finsupp.single 0 2) 1 + monomial (Finsupp.single 0 1) (-1) + C (7/20)

private theorem quadratic_eval (x : Fin 1 → ℝ) :
    eval x quadratic = (x 0 - 1/2)^2 + 1/10 := by
  simp [quadratic, eval_monomial, Finsupp.prod_single_index]
  ring

-- A fixed-degree coefficient test fails, but eventual positivity succeeds.
example : bernsteinCoeff (fun _ => 2) quadratic (fun _ => 1) = -3/20 := by
  norm_num [quadratic, bernsteinCoeff_add, bernsteinCoeff_monomial,
    Fin.prod_univ_one, Finsupp.single_apply, Nat.choose]

example : ∃ N : ℕ, 0 < N ∧ ∀ n : Fin 1 → ℕ, (∀ i, N ≤ n i) →
    ∀ k, (∀ i, k i ≤ n i) → 0 < bernsteinCoeff n quadratic k := by
  apply exists_pos_bernsteinCoeff_of_pos
  intro x _
  rw [quadratic_eval]
  positivity

-- Exact scaling regression: the error constant is that of the pullback.
example : bernsteinErrorConstant
    (monomial (Finsupp.single (0 : Fin 1) 2) (100 : ℝ)) = 400 := by
  norm_num [Fin.sum_univ_one, Finsupp.single_apply]

example : |bernsteinCoeff (fun _ : Fin 1 => 4)
      (monomial (Finsupp.single 0 2) (100 : ℝ)) (fun _ => 2) -
    eval (fun _ => (1/2 : ℝ)) (monomial (Finsupp.single 0 2) (100 : ℝ))| = 25/3 := by
  norm_num [bernsteinCoeff_monomial, Fin.prod_univ_one, Finsupp.single_apply,
    Nat.choose, eval_monomial, Finsupp.prod_single_index]

-- Scaling the original polynomial on [0, 10] changes the error constant.
private theorem scaled_square :
    boxPullback (fun _ : Fin 1 => 0) (fun _ => 10) (X 0 ^ 2) =
      monomial (Finsupp.single 0 2) (100 : ℝ) := by
  simp only [boxPullback, map_pow, eval₂Hom_X', sub_zero, map_zero, zero_add]
  rw [mul_pow, ← map_pow, X_pow_eq_monomial, C_mul_monomial]
  norm_num

example : bernsteinErrorConstant
    (boxPullback (fun _ : Fin 1 => 0) (fun _ => 10) (X 0 ^ 2)) = 400 := by
  rw [scaled_square]
  norm_num [Fin.sum_univ_one, Finsupp.single_apply]

-- Empty-variable constants have zero approximation error and a positive threshold.
example : ∃ N : ℕ, 0 < N ∧ ∀ n : Fin 0 → ℕ, (∀ i, N ≤ n i) →
    ∀ k, (∀ i, k i ≤ n i) → 0 < bernsteinCoeff n (C 3) k := by
  apply exists_pos_bernsteinCoeff_of_pos
  intro x _
  norm_num

private theorem quadratic_error : bernsteinErrorConstant quadratic = 5 := by
  classical
  have hs : quadratic.support ⊆ {Finsupp.single 0 2, Finsupp.single 0 1, 0} := by
    unfold quadratic
    apply support_add.trans
    apply Finset.union_subset
    · apply support_add.trans
      apply Finset.union_subset
      · exact support_monomial_subset.trans (by simp)
      · exact support_monomial_subset.trans (by simp)
    · exact support_monomial_subset.trans (by simp)
  unfold bernsteinErrorConstant
  rw [Finsupp.sum_of_support_subset _ hs _ (by intro d _; simp)]
  norm_num [quadratic, AddMonoidAlgebra.coeff_add, coeff_monomial, coeff_C, Fin.sum_univ_one,
    Finsupp.single_apply, Finsupp.ext_iff, Fin.forall_fin_one]

private theorem quadratic_degree (i : Fin 1) : quadratic.degreeOf i ≤ 2 := by
  unfold quadratic
  repeat apply (degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
  all_goals first
    | solve | simp
    | rw [degreeOf_monomial_eq _ _ (by norm_num)]
      fin_cases i; norm_num [Finsupp.single_apply]

-- A discharged numerical threshold, not just an existential result.
example (n : Fin 1 → ℕ) (hn : ∀ i, 100 ≤ n i) (k : Fin 1 → ℕ)
    (hk : ∀ i, k i ≤ n i) : 0 < bernsteinCoeff n quadratic k := by
  apply bernsteinCoeff_pos_of_error_lt (N := 100) (μ := 1/10) (by norm_num)
    (fun i => by have := quadratic_degree i; omega) hn
  · intro x _
    rw [quadratic_eval]
    have := sq_nonneg (x 0 - 1/2)
    linarith
  · rw [quadratic_error]
    norm_num
  · exact hk

-- Genuinely mixed polynomial: positivity is not a tensor-product assumption.
example : ∃ N : ℕ, 0 < N ∧ ∀ n : Fin 2 → ℕ, (∀ i, N ≤ n i) →
    ∀ k, (∀ i, k i ≤ n i) →
      0 < bernsteinCoeff n ((X 0 - X 1)^2 + C (1/10)) k := by
  apply exists_pos_bernsteinCoeff_of_pos
  intro x _
  simp only [map_add, map_pow, map_sub, eval_X, eval_C]
  positivity

-- Shifted box with one collapsed coordinate and a nonconstant remaining one.
example : ∃ N : ℕ, 0 < N ∧ ∀ n : Fin 2 → ℕ, (∀ i, N ≤ n i) →
    ∀ k, (∀ i, k i ≤ n i) →
      0 < bernsteinCoeff n (boxPullback ![2, 7] ![6, 7] (X 0 * X 1 + C 1)) k := by
  apply exists_pos_bernsteinCoeff_box_of_pos (by intro i; fin_cases i <;> norm_num)
  intro x hx
  simp only [map_add, map_mul, eval_X, eval_C]
  have h0 : 0 ≤ x 0 := (by norm_num : (0 : ℝ) ≤ 2).trans (hx 0).1
  have h1 : 0 ≤ x 1 := (by norm_num : (0 : ℝ) ≤ 7).trans (hx 1).1
  positivity

-- Fully collapsed box: positivity is needed only at its one point.
example : ∃ N : ℕ, 0 < N ∧ ∀ n : Fin 2 → ℕ, (∀ i, N ≤ n i) →
    ∀ k, (∀ i, k i ≤ n i) →
      0 < bernsteinCoeff n (boxPullback ![3, 1] ![3, 1] (X 0 - X 1)) k := by
  apply exists_pos_bernsteinCoeff_box_of_pos (by intro i; exact le_rfl)
  intro x hx
  have h0 : x 0 = 3 := le_antisymm (hx 0).2 (hx 0).1
  have h1 : x 1 = 1 := le_antisymm (hx 1).2 (hx 1).1
  norm_num [h0, h1]

-- A zero inside the cube prevents strictly positive coefficients at every
-- admissible degree, not merely at one low degree.
example (n : Fin 1 → ℕ)
    (hn : ∀ i, ((X 0 - C (1/2))^2 : MvPolynomial (Fin 1) ℝ).degreeOf i ≤ n i) :
    ¬ (∀ k : (i : Fin 1) → Fin (n i + 1),
      0 < bernsteinCoeff n ((X 0 - C (1/2))^2) (fun i => k i)) := by
  intro hc
  have h := eval_pos_of_bernsteinCoeff hn (x := fun _ => 1/2) (by intro i; norm_num) hc
  norm_num at h

#print axioms abs_bernsteinCoeff_sub_eval_le
#print axioms le_bernsteinCoeff_of_cube_lower_bound
#print axioms exists_pos_bernsteinCoeff_of_pos
#print axioms exists_pos_bernsteinCoeff_box_of_pos

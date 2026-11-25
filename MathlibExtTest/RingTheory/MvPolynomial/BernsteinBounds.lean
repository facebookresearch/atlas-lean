/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.RingTheory.MvPolynomial.BernsteinBounds
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fin.VecNotation

open MvPolynomial

-- A tensor basis function can be negative outside the unit cube; the
-- enclosure theorem must retain its domain hypothesis.
example : eval ![2, (1 / 2 : ℝ)] (bernstein ![1, 1] ![0, 0]) = -1 / 2 := by
  norm_num [eval_bernstein, bernsteinPolynomial, Fin.prod_univ_two]

-- Partition of unity still holds there, even with a zero coordinate degree.
example : (∑ k : (i : Fin 2) → Fin (![0, 2] i + 1),
    eval ![-7, 3] (bernstein ![0, 2] (fun i => k i))) = 1 :=
  sum_eval_bernstein _ _

private theorem xy_degree (i : Fin 2) :
    (X 0 * X 1 : MvPolynomial (Fin 2) ℝ).degreeOf i ≤ 1 := by
  apply (degreeOf_mul_le _ _ _).trans
  fin_cases i <;> simp [degreeOf_X]

private theorem xy_pullback :
    boxPullback ![-1, 3] ![2, 5] (X 0 * X 1 : MvPolynomial (Fin 2) ℝ) =
      C (-3) + (9 : ℝ) • X 0 + (-2 : ℝ) • X 1 + (6 : ℝ) • (X 0 * X 1) := by
  norm_num [boxPullback, smul_eq_C_mul, map_ofNat]
  ring

private theorem xy_coeff (k : Fin 2 → Fin 2) :
    bernsteinCoeff (fun _ => 1)
      (boxPullback ![-1, 3] ![2, 5] (X 0 * X 1)) (fun i => k i) =
        ![![-3, -5], ![6, 10]] (k 0) (k 1) := by
  rw [xy_pullback]
  generalize h : k 0 = i
  generalize h' : k 1 = j
  fin_cases i <;> fin_cases j <;>
    norm_num [bernsteinCoeff_add, bernsteinCoeff_smul, X, monomial_mul_monomial,
      bernsteinCoeff_monomial, Fin.prod_univ_two, Finsupp.single_apply, h, h', Nat.choose]

-- A genuinely shifted/scaled box and mixed term: all four corner coefficients
-- are used, including negative coefficients. Bounds include the endpoints.
example {x y : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 2) (hy : y ∈ Set.Icc (3 : ℝ) 5) :
    x * y ∈ Set.Icc (-5 : ℝ) 10 := by
  have h := eval_mem_Icc_of_bernsteinCoeff_box (n := fun _ : Fin 2 => 1)
    (p := X 0 * X 1) xy_degree (a := ![-1, 3]) (b := ![2, 5])
    (by intro i; fin_cases i <;> norm_num) (x := ![x, y])
    (by intro i; fin_cases i; exact hx; exact hy)
    (L := -5) (U := 10)
    (by
      intro k
      rw [xy_coeff]
      generalize k 0 = i
      generalize k 1 = j
      fin_cases i <;> fin_cases j <;> norm_num)
    (by
      intro k
      rw [xy_coeff]
      generalize k 0 = i
      generalize k 1 = j
      fin_cases i <;> fin_cases j <;> norm_num)
  simpa using h

-- Positivity of coefficients is sufficient, not necessary at a fixed degree:
-- (x - 1/2)^2 + 1/100 is strictly positive but has a negative middle coefficient.
example : bernsteinCoeff (fun _ : Fin 1 => 2)
    (monomial (Finsupp.single 0 2) 1 + monomial (Finsupp.single 0 1) (-1) + C (26 / 100))
    (fun _ => 1) = -24 / 100 := by
  norm_num [bernsteinCoeff_add, bernsteinCoeff_monomial, Fin.prod_univ_one,
    Finsupp.single_apply, Nat.choose]

example (x : ℝ) : 0 < (x - 1 / 2) ^ 2 + 1 / 100 := by positivity

-- A nonconstant positive example uses the unit-cube positivity API.
example {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    0 < 1 + x * y := by
  have h := eval_pos_of_bernsteinCoeff (n := fun _ : Fin 2 => 1)
    (p := C 1 + X 0 * X 1)
    (fun i => (degreeOf_add_le _ _ _).trans (max_le (by simp) (xy_degree i)))
    (x := ![x, y]) (by intro i; fin_cases i; exact hx; exact hy)
    (by
      intro k
      simp only [bernsteinCoeff_add, bernsteinCoeff_C, X, monomial_mul_monomial,
        bernsteinCoeff_monomial, one_mul, mul_one]
      apply add_pos_of_pos_of_nonneg (by norm_num)
      apply Finset.prod_nonneg
      intro i _
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  simpa using h

-- Strict positivity includes the boundary and works with degree zero.
example (x : Fin 2 → ℝ) (hx : ∀ i, x i ∈ Set.Icc (-2 : ℝ) 4) :
    0 < eval x (C 7 : MvPolynomial (Fin 2) ℝ) := by
  apply eval_pos_of_bernsteinCoeff_box (n := fun _ => 0)
    (a := fun _ => -2) (b := fun _ => 4) (by simp) (by norm_num) hx
  intro k
  norm_num [boxPullback]

-- One coordinate collapses while the other remains an interval.
example (t : Fin 2 → ℝ) :
    eval t (boxPullback ![2, -1] ![2, 3] (X 0 * X 1)) =
      2 * (-1 + 4 * t 1) := by
  rw [eval_boxPullback]
  norm_num

-- A fully discharged enclosure on a partially collapsed box: x is fixed at 2.
example {y : ℝ} (hy : y ∈ Set.Icc (-1 : ℝ) 3) :
    2 * y ∈ Set.Icc (-2 : ℝ) 6 := by
  have hpull : boxPullback ![2, -1] ![2, 3] (X 0 * X 1 : MvPolynomial (Fin 2) ℝ) =
      C (-2) + (8 : ℝ) • X 1 := by
    norm_num [boxPullback, smul_eq_C_mul, map_ofNat]
    ring
  have hc (k : Fin 2 → Fin 2) :
      bernsteinCoeff (fun _ => 1) (boxPullback ![2, -1] ![2, 3] (X 0 * X 1))
        (fun i => k i) ∈ Set.Icc (-2 : ℝ) 6 := by
    rw [hpull]
    generalize h : k 0 = i
    generalize h' : k 1 = j
    fin_cases i <;> fin_cases j <;>
      norm_num [bernsteinCoeff_add, bernsteinCoeff_smul, X,
        bernsteinCoeff_monomial, Fin.prod_univ_two, Finsupp.single_apply, h, h', Nat.choose]
  have h := eval_mem_Icc_of_bernsteinCoeff_box (n := fun _ : Fin 2 => 1)
    (p := X 0 * X 1) xy_degree (a := ![2, -1]) (b := ![2, 3])
    (by intro i; fin_cases i <;> norm_num) (x := ![2, y])
    (by intro i; fin_cases i; norm_num; exact hy)
    (fun k => (hc k).1) (fun k => (hc k).2)
  simpa using h

example (c : ℝ) :
    eval (Fin.elim0 : Fin 0 → ℝ) (C c) ∈ Set.Icc c c := by
  apply eval_mem_Icc_of_bernsteinCoeff_box (n := fun _ => 0)
    (a := Fin.elim0) (b := Fin.elim0)
    (by intro i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i)
    (by intro i; exact Fin.elim0 i)
  · simp [boxPullback]
  · simp [boxPullback]

-- A collapsed box is permitted, without division by a nonzero width.
example (p : MvPolynomial (Fin 2) ℝ) (a : Fin 2 → ℝ) (L U : ℝ)
    (hL : ∀ k : (i : Fin 2) → Fin (p.degreeOf i + 1),
      L ≤ bernsteinCoeff (fun i => p.degreeOf i) (boxPullback a a p) (fun i => k i))
    (hU : ∀ k : (i : Fin 2) → Fin (p.degreeOf i + 1),
      bernsteinCoeff (fun i => p.degreeOf i) (boxPullback a a p) (fun i => k i) ≤ U) :
    eval a p ∈ Set.Icc L U := by
  exact eval_mem_Icc_of_bernsteinCoeff_box (fun _ => le_rfl)
    (fun _ => le_rfl) (fun _ => ⟨le_rfl, le_rfl⟩) hL hU

#print axioms MvPolynomial.eval_mem_Icc_of_bernsteinCoeff_box
#print axioms MvPolynomial.eval_pos_of_bernsteinCoeff_box
#print axioms MvPolynomial.eval_mem_Icc_bernsteinCoeff_box

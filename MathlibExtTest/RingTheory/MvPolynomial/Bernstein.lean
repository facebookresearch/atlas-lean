/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.RingTheory.MvPolynomial.Bernstein
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation

open MvPolynomial

-- A mixed monomial has genuinely fractional coefficients at unequal degrees.
example : bernsteinCoeff (fun i : Fin 2 => if i = 0 then 3 else 2)
    (monomial (Finsupp.single 0 2 + Finsupp.single 1 1) 1)
    (fun i => if i = 0 then 2 else 1) = 1 / 6 := by
  norm_num [bernsteinCoeff_monomial, Fin.prod_univ_two, Finsupp.single_apply]

-- The empty variable type is allowed; this is a polynomial identity, not only
-- a pointwise assertion on a nonempty cube.
example (c : ℝ) : (C c : MvPolynomial (Fin 0) ℝ) =
    ∑ k : (i : Fin 0) → Fin (0 + 1),
      C (bernsteinCoeff (fun _ => 0) (C c) (fun i => k i)) *
        bernstein (fun _ => 0) (fun i => k i) := by
  apply eq_sum_bernstein
  intro i
  exact Fin.elim0 i

example (n k : Fin 2 → ℕ) : bernsteinCoeff n (0 : MvPolynomial (Fin 2) ℝ) k = 0 := by
  simp

example (n k : Fin 2 → ℕ) (c : ℝ) : bernsteinCoeff n (C c) k = c := by
  simp

-- Without the degree hypothesis, the coefficient formula remains defined:
-- its zero binomial denominator gives zero rather than an invalid fraction.
example : bernsteinCoeff (fun _ : Fin 1 => 0)
    (monomial (Finsupp.single 0 1) 1) (fun _ => 1) = 0 := by
  norm_num [bernsteinCoeff_monomial, Fin.prod_univ_one, Finsupp.single_apply, Nat.choose]

-- Smith (2012), Example 3.1 / Table 3.2: all twelve coefficients of
-- 2*x^3 - x^2*y/2 + 7*y^2 - 4*x*y + 3, at bidegree (3,2).
private noncomputable def sample : MvPolynomial (Fin 2) ℝ :=
  monomial (Finsupp.single 0 3) 2 +
  monomial (Finsupp.single 0 2 + Finsupp.single 1 1) (-1 / 2) +
  monomial (Finsupp.single 1 2) 7 +
  monomial (Finsupp.single 0 1 + Finsupp.single 1 1) (-4) + C 3

example (i : Fin 4) (j : Fin 3) :
    bernsteinCoeff ![3, 2] sample ![i, j] =
      ![![3, 3, 10], ![3, 7 / 3, 26 / 3],
        ![3, 19 / 12, 43 / 6], ![5, 11 / 4, 15 / 2]] i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [sample, bernsteinCoeff_add, bernsteinCoeff_monomial,
      Fin.prod_univ_two, Finsupp.single_apply, Nat.choose]

private theorem sample_degree (i : Fin 2) : sample.degreeOf i ≤ ![3, 2] i := by
  unfold sample
  repeat apply (degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
  all_goals first
    | solve | simp
    | rw [degreeOf_monomial_eq _ _ (by norm_num)]
      fin_cases i <;> norm_num [Finsupp.single_apply]

-- The full expansion works for arbitrary arguments, not only on the cube.
example (x y : ℝ) : eval ![x, y] sample =
    ∑ k : (i : Fin 2) → Fin (![3, 2] i + 1),
      bernsteinCoeff ![3, 2] sample (fun i => k i) *
        eval ![x, y] (bernstein ![3, 2] (fun i => k i)) :=
  eval_eq_sum_bernstein sample_degree _

-- Outside the cube, the weights still reconstruct exactly (not an enclosure).
example : (∑ k : (i : Fin 2) → Fin (![3, 2] i + 1),
    bernsteinCoeff ![3, 2] sample (fun i => k i) *
      eval ![-1, 2] (bernstein ![3, 2] (fun i => k i))) = 36 := by
  rw [← eval_eq_sum_bernstein sample_degree]
  norm_num [sample, eval_monomial, Finsupp.prod_add_index, Finsupp.prod_single_index]

-- A constant coordinate degree does not require a positive degree vector.
example (x : Fin 2 → ℝ) : eval x (C (-3) : MvPolynomial (Fin 2) ℝ) =
    ∑ k : (i : Fin 2) → Fin (![0, 2] i + 1),
      bernsteinCoeff ![0, 2] (C (-3)) (fun i => k i) *
        eval x (bernstein ![0, 2] (fun i => k i)) := by
  apply eval_eq_sum_bernstein
  intro i
  rw [degreeOf_C]
  exact Nat.zero_le _

-- Scalar multiplication and cancellation use the public coefficient API.
example (n k : Fin 2 → ℕ) (p : MvPolynomial (Fin 2) ℝ) :
    bernsteinCoeff n ((2 : ℝ) • p + (-2 : ℝ) • p) k = 0 := by
  simp

#print axioms MvPolynomial.eq_sum_bernstein

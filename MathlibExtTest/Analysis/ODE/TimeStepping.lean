/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.TimeStepping
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Fin.VecNotation

open Set
open MathlibExt.Analysis.ODE.TimeStepping
open scoped Matrix BigOperators

-- The decay solution has a uniform quadratic explicit-Euler local error.
example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, t + h ≤ 1 →
      ‖Real.exp (-1 * (t + h)) - (Real.exp (-1 * t) + h • (-1 * Real.exp (-1 * t)))‖ ≤
        C * h ^ 2 :=
  decay_local_truncation_le (lam := 1) (T := 1) (by norm_num) (by norm_num)

-- Euler powers instantiate the numerical recurrence for scalar decay `x' = -x`.
example :
    ∃ x : ℝ → ℝ, x 0 = 1 ∧ (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt x (-1 * x t) t) ∧
      ∃ C : ℝ, ∀ h ∈ Ioc (0 : ℝ) 1, ∀ X : ℕ → ℝ, X 0 = 1 →
        (∀ n, X (n + 1) = X n + h • (-1 * X n)) →
        ∀ n : ℕ, (n : ℝ) * h ≤ 1 → ‖X n - x ((n : ℝ) * h)‖ ≤ C * h :=
  decay_global_convergence (lam := 1) (T := 1) (by norm_num) (by norm_num)

-- Numeric instance: the Euler value at `lam = 1`, `h = 1 / 10`, `n = 10`.
example : (1 - 1 * (1 / 10 : ℝ)) ^ 10 = (9 / 10) ^ 10 := by norm_num

-- Numeric instance: the analytic value is `Real.exp (-1)`.
example : Real.exp (-1 * (10 * (1 / 10 : ℝ))) = Real.exp (-1) := by
  congr 1
  norm_num

-- Numeric instance: the certified bound holds with explicit constant `C = 1`.
example : |(9 / 10 : ℝ) ^ 10 - Real.exp (-1)| ≤ 1 * (1 / 10) :=
  decay_euler_numeric_bound

-- FTCS positivity is sharp: at `r = 1 / 2` the center coefficient vanishes.
example : (1 - 2 * (1 / 2 : ℝ)) = 0 := by norm_num

-- At `r = 3 / 4` the alternating mode amplifies by a factor of `2` in abs value.
example : |1 - 4 * (3 / 4 : ℝ)| = 2 := by norm_num

-- The FTCS witness at `m = 4`, `r = 3 / 4`: one step scales the mode by `-2`.
example : ftcsStep (m := 4) (3 / 4 : ℝ) altMode =
    (1 - 4 * (3 / 4 : ℝ)) • altMode :=
  ftcsStep_altMode (m := 4) (⟨2, rfl⟩ : Even 4) (3 / 4)

-- The amplified-mode witness at `m = 4`, `r = 3 / 4`: the sup norm strictly grows.
example : ‖(altMode : Fin 4 → ℝ)‖ < ‖ftcsStep (3 / 4 : ℝ) (altMode : Fin 4 → ℝ)‖ :=
  norm_altMode_lt_norm_ftcsStep (m := 4) (by norm_num) (⟨2, rfl⟩ : Even 4) (by norm_num)

-- Scalar positivity instance: decay from `x = 5` with `h = 1 / 2 ≤ 1 / 1`.
example : (0 : ℝ) ≤ (1 - 1 * (1 / 2)) * 5 :=
  scalarEuler_nonneg (lam := 1) (h := 1 / 2) (x := 5) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

-- FTCS conservation instance on the 3-point periodic grid.
example : ∑ i, ftcsStep (m := 3) (1 / 2 : ℝ) (![1, 2, 3] : Fin 3 → ℝ) i =
    ∑ i, (![1, 2, 3] : Fin 3 → ℝ) i :=
  ftcsStep_conserves_sum (m := 3) (1 / 2) ![1, 2, 3]

-- Defects through the ten-step decay recurrence `e_{j+1} = (9 / 10) e_j + η_j`.

section DefectRecurrence

open Finset

/-- **Early and late defects weigh differently.** From a zero initial defect, a unit residual at
the first step leaves `e_10 = (9 / 10) ^ 9`, and a unit residual at the last step leaves
`e_10 = 1`. -/
lemma tenStep_defect_weights_differ {e e' : ℕ → ℝ} (h0 : e 0 = 0) (h0' : e' 0 = 0)
    (h : ∀ j < 10, e (j + 1) = 9 / 10 * e j + if j = 0 then 1 else 0)
    (h' : ∀ j < 10, e' (j + 1) = 9 / 10 * e' j + if j = 9 then 1 else 0) :
    e 10 = (9 / 10) ^ 9 ∧ e' 10 = 1 ∧ e 10 < e' 10 := by
  have ha := tenStep_defect_eq (η := fun j => if j = 0 then 1 else 0) h
  have hb := tenStep_defect_eq (η := fun j => if j = 9 then 1 else 0) h'
  rw [h0] at ha
  rw [h0'] at hb
  simp only [sum_range_succ, sum_range_zero] at ha hb
  norm_num at ha hb
  refine ⟨by rw [ha]; norm_num, hb, by rw [ha, hb]; norm_num⟩

-- A unit residual at the first step from a zero initial defect: the weighted bound `(9 / 10) ^ 9`
-- is attained, while the unweighted bound only gives `1`.
example {e : ℕ → ℝ} (h0 : e 0 = 0)
    (h : ∀ j < 10, e (j + 1) = 9 / 10 * e j + if j = 0 then 1 else 0) :
    |e 10| ≤ (9 / 10) ^ 9 ∧ |e 10| ≤ 1 ∧ |e 10| = (9 / 10) ^ 9 := by
  have hw := tenStep_defect_le h
  have hu := tenStep_defect_le_unweighted h
  have he : e 10 = (9 / 10) ^ 9 := by
    have := tenStep_defect_eq h
    rw [h0] at this
    norm_num [sum_range_succ] at this
    rw [this]
    norm_num
  rw [h0] at hw hu
  norm_num [sum_range_succ] at hw hu
  refine ⟨by linarith, by linarith, by rw [he]; norm_num⟩

end DefectRecurrence

#print axioms decay_local_truncation_le
#print axioms decay_global_convergence
#print axioms eulerStep
#print axioms eulerStep_conserves_dotProduct
#print axioms eulerStep_iterate_conserves_dotProduct
#print axioms scalarEuler_nonneg
#print axioms scalarEuler_neg_of_large_step
#print axioms ftcsStep
#print axioms ftcsStep_conserves_sum
#print axioms ftcsStep_convex
#print axioms ftcsStep_nonneg
#print axioms altMode
#print axioms ftcsStep_altMode
#print axioms altMode_amplification_gt_one
#print axioms altMode_ne_zero
#print axioms norm_altMode_lt_norm_ftcsStep
#print axioms decay_euler_error_le
#print axioms decay_euler_numeric_bound
#print axioms tenStep_defect_eq
#print axioms tenStep_defect_le
#print axioms tenStep_defect_le_unweighted
#print axioms tenStep_defect_weights_differ

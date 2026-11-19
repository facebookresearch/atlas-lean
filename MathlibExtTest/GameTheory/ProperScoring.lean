/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.GameTheory.ProperScoring
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Tests for proper scoring rules on two outcomes

Binary checks for the quadratic rule gap (P2/P5), the log-score
disjunction at a full-support pair and a support-violation pair (P3/P5),
the real log-rule witness (P3n/P5) and the linear-rule witness (P4/P5).
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExtTest.GameTheory.ProperScoring

open scoped BigOperators
open MathlibExt.GameTheory.ProperScoring

/-- P5: quadratic rule strictly rewards truthful reporting on two outcomes. -/
theorem quadratic_binary_gap :
    expectedScore (Fin 2) (quadraticRule (Fin 2)) (fun _ => 1 / 2)
        (fun i => if i = 0 then 1 else 0) <
      expectedScore (Fin 2) (quadraticRule (Fin 2)) (fun _ => 1 / 2)
        (fun _ => 1 / 2) := by
  have hq0 : (if True then (1 : ℝ) else 0) = 1 := by simp
  have hq1 : (if (1 : Fin 2) = 0 then (1 : ℝ) else 0) = 0 := by simp
  have hpp : expectedScore (Fin 2) (quadraticRule (Fin 2)) (fun _ => 1 / 2)
      (fun _ => 1 / 2) = 1 / 4 := by
    simp only [expectedScore, quadraticRule, Fin.sum_univ_two]
    norm_num
  have hpq : expectedScore (Fin 2) (quadraticRule (Fin 2)) (fun _ => 1 / 2)
      (fun i => if i = 0 then 1 else 0) = 0 := by
    simp only [expectedScore, quadraticRule, Fin.sum_univ_two, hq0, hq1]
    norm_num
  rw [hpq, hpp]
  norm_num

/-- P5: P3 second disjunct at a full-support binary pair. -/
theorem logScore_binary_fullSupport :
    ∑ i : Fin 2, (1 / 2 : ℝ) * Real.log (if i = 0 then 1 / 4 else 3 / 4) <
      ∑ _i : Fin 2, (1 / 2 : ℝ) * Real.log (1 / 2) := by
  have h0 : (if True then (1 / 4 : ℝ) else 3 / 4) = 1 / 4 := by simp
  have h1' : (if (1 : Fin 2) = 0 then (1 / 4 : ℝ) else 3 / 4) = 3 / 4 := by
    simp
  simp only [Fin.sum_univ_two, h0, h1']
  have h1 : (1 / 4 : ℝ) * (3 / 4) = 3 / 16 := by norm_num
  have hm := Real.log_mul (show (1 / 4 : ℝ) ≠ 0 by norm_num)
    (show (3 / 4 : ℝ) ≠ 0 by norm_num)
  rw [h1] at hm
  have h2 : (1 / 2 : ℝ) * (1 / 2) = 1 / 4 := by norm_num
  have hm2 := Real.log_mul (show (1 / 2 : ℝ) ≠ 0 by norm_num)
    (show (1 / 2 : ℝ) ≠ 0 by norm_num)
  rw [h2] at hm2
  have hlt : Real.log (3 / 16 : ℝ) < Real.log (1 / 4 : ℝ) := by
    apply Real.log_lt_log (by norm_num) (by norm_num)
  linarith [hm, hm2, hlt]

/-- P5: P3 first disjunct at a binary support-violation pair. -/
theorem logScore_binary_supportViolation :
    ∃ i : Fin 2, 0 < (1 / 2 : ℝ) ∧
      (if i = 0 then (1 : ℝ) else 0) = 0 := by
  exact ⟨1, by norm_num, by simp⟩

/-- P5: linear-rule witness evaluates to a strict gap on two outcomes. -/
theorem linear_binary_gap :
    expectedScore (Fin 2) (linearRule (Fin 2))
        (fun i => if i = 0 then 3 / 4 else 1 / 4)
        (fun i => if i = 0 then 3 / 4 else 1 / 4) <
      expectedScore (Fin 2) (linearRule (Fin 2))
        (fun i => if i = 0 then 3 / 4 else 1 / 4)
        (fun i => if i = 0 then 1 else 0) := by
  have hp0 : (if True then (3 / 4 : ℝ) else 1 / 4) = 3 / 4 := by simp
  have hp1 : (if (1 : Fin 2) = 0 then (3 / 4 : ℝ) else 1 / 4) = 1 / 4 := by
    simp
  have hq0 : (if True then (1 : ℝ) else 0) = 1 := by simp
  have hq1 : (if (1 : Fin 2) = 0 then (1 : ℝ) else 0) = 0 := by simp
  have hpp : expectedScore (Fin 2) (linearRule (Fin 2))
      (fun i => if i = 0 then 3 / 4 else 1 / 4)
      (fun i => if i = 0 then 3 / 4 else 1 / 4) = 5 / 8 := by
    simp only [expectedScore, linearRule, Fin.sum_univ_two, hp0, hp1]
    norm_num
  have hpq : expectedScore (Fin 2) (linearRule (Fin 2))
      (fun i => if i = 0 then 3 / 4 else 1 / 4)
      (fun i => if i = 0 then 1 else 0) = 3 / 4 := by
    simp only [expectedScore, linearRule, Fin.sum_univ_two, hp0, hp1, hq0,
      hq1]
    norm_num
  rw [hpp, hpq]
  norm_num

/-- P5: real log-rule witness evaluates to a strict gap on two outcomes. -/
theorem logRule_binary_gap :
    expectedScore (Fin 2) (logRule (Fin 2)) (fun _ => 1 / 2)
        (fun _ => 1 / 2) <
      expectedScore (Fin 2) (logRule (Fin 2)) (fun _ => 1 / 2)
        (fun i => if i = 0 then 1 else 0) := by
  have hq0 : (if True then (1 : ℝ) else 0) = 1 := by simp
  have hq1 : (if (1 : Fin 2) = 0 then (1 : ℝ) else 0) = 0 := by simp
  have hpp : expectedScore (Fin 2) (logRule (Fin 2)) (fun _ => 1 / 2)
      (fun _ => 1 / 2) = Real.log (1 / 2) := by
    simp only [expectedScore, logRule, Fin.sum_univ_two]
    ring
  have hpq : expectedScore (Fin 2) (logRule (Fin 2)) (fun _ => 1 / 2)
      (fun i => if i = 0 then 1 else 0) = 0 := by
    simp only [expectedScore, logRule, Fin.sum_univ_two, hq0, hq1,
      Real.log_one, Real.log_zero]
    ring
  have hneg : Real.log ((1 / 2 : ℝ)) < 0 := by
    rw [Real.log_neg_iff (by norm_num)]
    norm_num
  rw [hpp, hpq]
  exact hneg

end MathlibExtTest.GameTheory.ProperScoring

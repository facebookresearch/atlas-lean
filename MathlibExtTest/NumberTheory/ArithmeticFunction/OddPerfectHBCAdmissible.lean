/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectHBCAdmissible
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectHBCAdmissible` -/

namespace MathlibExtTest.NumberTheory.ArithmeticFunction.OddPerfectHBCAdmissible

-- At `k = 1` the theorem reads `(1 - 1/2) ≤ (1 - 1/3)`.
example : (1:ℝ) - 1 / 2 ≤ 1 - 1 / 3 := by
  have hz : Monotone (fun _ : Fin 1 => (2:ℝ)) := monotone_const
  have hy : Monotone (fun _ : Fin 1 => (3:ℝ)) := monotone_const
  have hz1 : ∀ i : Fin 1, 1 < (fun _ : Fin 1 => (2:ℝ)) i := by
    intro i
    change (1:ℝ) < 2
    norm_num
  have hy1 : ∀ i : Fin 1, 1 < (fun _ : Fin 1 => (3:ℝ)) i := by
    intro i
    change (1:ℝ) < 3
    norm_num
  have hprefix : ∀ l ≤ 1,
      ∏ i ∈ Finset.univ.filter (fun i : Fin 1 => (i : ℕ) < l), (fun _ : Fin 1 => (2:ℝ)) i ≤
      ∏ i ∈ Finset.univ.filter (fun i : Fin 1 => (i : ℕ) < l), (fun _ : Fin 1 => (3:ℝ)) i := by
    intro l hl
    have h0 : 0 ≤ l := Nat.zero_le l
    interval_cases l
    · have e0 : Finset.univ.filter (fun i : Fin 1 => (i : ℕ) < 0) = ∅ := by decide
      rw [e0]
      simp
    · have e1 : Finset.univ.filter (fun i : Fin 1 => (i : ℕ) < 1) = {0} := by decide
      rw [e1, Finset.prod_singleton, Finset.prod_singleton]
      change (2:ℝ) ≤ 3
      norm_num
  have h := MetaMathlibExt.prod_one_sub_inv_le_of_prefix_prod_le 1
    (fun _ : Fin 1 => (2:ℝ)) (fun _ : Fin 1 => (3:ℝ)) hz hy hz1 hy1 hprefix
  rw [Fin.prod_univ_one, Fin.prod_univ_one] at h
  exact h.1

-- If `z ≠ y`, the inequality is strict.
example (k : ℕ) (z y : Fin k → ℝ) (hz : Monotone z) (hy : Monotone y)
    (hz1 : ∀ i, 1 < z i) (hy1 : ∀ i, 1 < y i)
    (hprefix : ∀ l ≤ k, ∏ i ∈ Finset.univ.filter (fun i : Fin k => (i : ℕ) < l), z i ≤
      ∏ i ∈ Finset.univ.filter (fun i : Fin k => (i : ℕ) < l), y i)
    (hne : z ≠ y) :
    ∏ i, (1 - 1 / z i) < ∏ i, (1 - 1 / y i) := by
  have h := MetaMathlibExt.prod_one_sub_inv_le_of_prefix_prod_le k z y hz hy hz1 hy1 hprefix
  exact lt_of_le_of_ne h.1 (fun heq => hne (h.2.mp heq))

end MathlibExtTest.NumberTheory.ArithmeticFunction.OddPerfectHBCAdmissible

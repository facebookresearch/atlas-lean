/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.NicomacheanAdjoinedProgression

/-! # Tests for adjoined Nicomachean sequences -/

open MetaMathlibExt

-- Starting from [2], adjoin 1, 3, 4, 5, … . The step at index 1 is the first unit step.
example :
    let x : ℕ → ℝ := fun j => if j = 0 then 1 else (j : ℝ) + 2
    x 2 = x 1 + 1 ∧ x 1 ≠ x 0 + 1 := by
  intro x
  let p (n : ℕ) := [2] ++ (List.range (n + 1)).map x
  have hpos (n : ℕ) : 0 < x n := by
    dsimp [x]
    split <;> positivity
  have hprefix (n : ℕ) : 2 * (p n).sum = ((n : ℝ) + 2) * ((n : ℝ) + 3) ∧
      nicomacheanNu (p n) = 0 := by
    induction n with
    | zero => norm_num [p, x, nicomacheanNu, List.range_succ]
    | succ n ih =>
      have hterm : x (n + 1) = (n : ℝ) + 3 := by
        simp only [x, Nat.add_one_ne_zero, ite_false, Nat.cast_add, Nat.cast_one]
        ring
      rw [show p n.succ = p n ++ [x (n + 1)] by
        simp only [p, Nat.succ_eq_add_one, List.range_succ (n := n + 1), List.map_append,
          List.map_singleton, List.append_assoc]]
      constructor
      · rw [List.sum_append, List.sum_singleton, hterm, Nat.cast_succ]
        linear_combination ih.1
      · simp only [nicomacheanNu, List.map_append, List.sum_append, List.map_singleton,
          List.sum_singleton] at ih ⊢
        rw [hterm]
        linear_combination ih.2 + ((n : ℝ) + 3) * ih.1
  refine ⟨nicomachean_adjoined_arithmeticProgression [2] x (fun n => (hpos n).ne') ?_
    (fun n => (hprefix n).2) 1 le_rfl, ?_⟩
  · exact fun n => ne_of_gt ((neg_neg_of_pos (hpos n)).trans (hpos (n + 1)))
  · norm_num [x]

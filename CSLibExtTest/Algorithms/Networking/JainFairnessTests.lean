/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Algorithms.Networking.JainFairness
import Mathlib.Data.Fin.VecNotation

/-! # Tests for the sharp bounds on Jain's fairness index -/

namespace Cslib.Algorithms.Networking.Aimd

-- Two equally served users out of three. The same support with unequal shares
-- has a strictly smaller index, even when the total is unchanged.
example : fairness ![0, 2, 2] = 2 / 3 := by
  let s : Finset (Fin 3) := {1, 2}
  have h : (![0, 2, 2] : Fin 3 → ℝ) = fun i => if i ∈ s then 2 else 0 := by
    funext i
    fin_cases i <;> norm_num [s, Fin.reduceEq]
  rw [h, fairness_eq_card_div_of_equal_shares s (by decide) (by norm_num)]
  norm_num [s]

example : fairness ![0, 1, 3] = 8 / 15 := by
  norm_num [fairness, Fin.sum_univ_three]

-- With just one positive share, it does not matter which user receives it.
example : fairness ![0, 5, 0] = 1 / 3 := by
  apply (fairness_eq_one_div_iff (n := 3) (by decide) _ _).2
  · refine ⟨1, by norm_num, ?_⟩
    intro i hi
    fin_cases i <;> norm_num at *
  · intro i
    fin_cases i <;> norm_num
  · intro h
    have := congrFun h 1
    norm_num at this

example : fairness (fun _ : Fin 4 => (7 : ℝ)) = 1 := by
  apply (fairness_eq_one_iff (n := 4) (by decide) _).2
  · exact fun _ _ => rfl
  · intro h
    have := congrFun h 0
    norm_num at this

-- For a single user the two endpoints coincide.
example (c : ℝ) (hc : 0 < c) : fairness (fun _ : Fin 1 => c) = 1 := by
  have h := fairness_mem_Icc_one_div (n := 1) (by decide) (fun _ => hc.le) (by
    intro h
    exact hc.ne' (congrFun h 0))
  norm_num at h
  exact h

-- A zero coordinate is allowed in the continuity domain; only the zero vector is excluded.
example : ContinuousWithinAt (fairness (n := 2)) {x | (∀ i, 0 ≤ x i) ∧ x ≠ 0} ![0, 1] := by
  apply continuousOn_fairness (by decide)
  constructor
  · intro i
    fin_cases i <;> norm_num
  · intro h
    have := congrFun h 1
    norm_num at this

end Cslib.Algorithms.Networking.Aimd

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Sequences.NewtonInequalities
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- A one-term sequence has no Newton inequalities and its peak is the endpoint.
example (a : ℕ → ℝ) (ha : 0 < a 0) :
    StrictMonoOn a (Set.Icc 0 0) ∧ StrictAntiOn a (Set.Icc 0 0) := by
  obtain ⟨m, hm, hinc, htail⟩ := unimodal_of_newton_inequalities (n := 0) (a := a)
    (by simpa using ha) (by intro j hj hjn; omega)
  obtain rfl := Nat.eq_zero_of_le_zero hm
  exact ⟨hinc, htail.resolve_right (fun h => (Nat.lt_irrefl 0) h.1)⟩

-- The row 1, 3, 3, 1 attains equality in Newton's inequalities and forces the plateau alternative.
example :
    let a := fun j => ((3 : ℕ).choose j : ℝ)
    ∃ m < 3, StrictMonoOn a (Set.Icc 0 m) ∧
      a m = a (m + 1) ∧ StrictAntiOn a (Set.Icc (m + 1) 3) := by
  intro a
  have hpos : ∀ j ≤ 3, 0 < a j := fun _ hj => Nat.cast_pos.mpr (Nat.choose_pos hj)
  obtain ⟨m, _, hinc, hdec | ⟨hm, heq, hdec⟩⟩ :=
    unimodal_of_newton_inequalities hpos (by
      intro j hj hjn
      interval_cases j <;> norm_num [a, Nat.choose])
  · have heq : a 1 = a 2 := by norm_num [a, Nat.choose]
    by_cases hm : m ≤ 1
    · exact (heq.not_gt (@hdec 1 ⟨hm, by decide⟩ 2 ⟨by omega, by decide⟩ (by decide))).elim
    · exact (heq.not_lt (@hinc 1 ⟨by decide, by omega⟩ 2 ⟨by decide, by omega⟩ (by decide))).elim
  · exact ⟨m, hm, hinc, heq, hdec⟩

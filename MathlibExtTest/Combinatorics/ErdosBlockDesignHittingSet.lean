/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ErdosBlockDesignHittingSet
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

open MathlibExt.Combinatorics.ErdosBlockDesignHittingSetWanted

-- The same density works against every proposed bound.
example : ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ C : ℕ, ∃ n : ℕ, ∃ blocks : Finset (Finset (Fin n)),
    (∀ A ∈ blocks, c * Real.sqrt n < A.card) ∧
    (∀ A ∈ blocks, ∀ D ∈ blocks, A ≠ D → (A ∩ D).card ≤ 1) ∧
    ∀ B : Finset (Fin n), ∃ A ∈ blocks, B ∩ A = ∅ ∨ C < (B ∩ A).card := by
  classical
  have h := conjecture_refuted
  unfold conjecture at h
  push +distrib Not at h
  simpa [Finset.card_eq_zero] using h

-- On three points, the pairs already rule out meeting every block exactly once.
private def triangle : Finset (Finset (Fin 3)) := {{0, 1}, {1, 2}, {0, 2}}

example :
    (∀ A ∈ triangle, (1 / 4 : ℝ) * Real.sqrt 3 < A.card) ∧
    (∀ A ∈ triangle, ∀ D ∈ triangle, A ≠ D → (A ∩ D).card ≤ 1) ∧
    ¬ ∃ B : Finset (Fin 3), ∀ A ∈ triangle, 0 < (B ∩ A).card ∧ (B ∩ A).card ≤ 1 := by
  refine ⟨?_, by decide, by decide⟩
  have hcard : ∀ A ∈ triangle, A.card = 2 := by decide
  intro A hA
  rw [hcard A hA]
  have hs : Real.sqrt 3 ≤ 2 := Real.sqrt_le_iff.mpr (by norm_num)
  norm_num
  linarith

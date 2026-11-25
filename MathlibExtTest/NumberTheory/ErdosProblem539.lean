/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.ErdosProblem539

open MathlibExt.NumberTheory.ErdosProblem539Wanted

example : cofactorThreshold 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply csSup_le'
  intro m hm
  simpa using hm ∅ rfl (by simp)

example (m : ℕ) : IsCofactorLowerBound 1 m ↔ m ≤ 1 := by
  constructor
  · intro hm
    simpa using hm {1} (by simp) (by simp)
  · intro hm A hcard hpos
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
    simpa using hm

-- The four ordered pairs from {6, 12} give just two distinct cofactors.
example : ¬ IsCofactorLowerBound 2 3 := by
  intro h
  have hcard := h {6, 12} (by decide) (by decide)
  exact (by decide : ¬ 3 ≤ 2) hcard

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.AcceleratedZeckendorfGameTermination
import Mathlib.Tactic.Linarith

open MetaMathlibExt

-- Even for zero starting tokens, the theorem rules out infinite play.
example : ¬ ∃ g : ℕ → ℕ →₀ ℕ,
    g 0 = 0 ∧ ∀ j, AccelZeckMove (g j) (g (j + 1)) := by
  simpa using (accelZeckGame_terminates_at_zeckendorf 0).1

-- The empty game ends at the empty state and has the exact bound zero.
example {L : ℕ} {g : ℕ → ℕ →₀ ℕ} (hg : IsAccelZeckGame 0 L g) : g L = 0 ∧ L = 0 := by
  obtain ⟨hfinal, hlength⟩ := (accelZeckGame_terminates_at_zeckendorf 0).2 L g hg
  refine ⟨hfinal.trans zeckendorfState_zero, ?_⟩
  have hlength' : (L : ℝ) ≤ 0 := by simpa using hlength
  exact Nat.eq_zero_of_le_zero (by exact_mod_cast hlength')

-- For 4 = F₃ + F₁ the index sum is 4 and there are two terms.
example {L : ℕ} {g : ℕ → ℕ →₀ ℕ} (hg : IsAccelZeckGame 4 L g) :
    g L = Finsupp.single 3 1 + Finsupp.single 1 1 ∧ (L : ℝ) ≤ 1 + Real.sqrt 5 := by
  obtain ⟨hfinal, hlength⟩ := (accelZeckGame_terminates_at_zeckendorf 4).2 L g hg
  refine ⟨hfinal.trans zeckendorfState_four, ?_⟩
  have hrep : ([4, 2] : List ℕ).IsZeckendorfRep := by simp [List.IsZeckendorfRep]
  have hzeck := Nat.zeckendorf_sum_fib hrep
  rw [show ([4, 2].map Nat.fib).sum = 4 by decide] at hzeck
  rw [hzeck] at hlength
  change (L : ℝ) ≤ (Real.sqrt 5 + 3) / 2 * 4 - 4 - (1 + Real.sqrt 5) / 2 * 2 at hlength
  linarith only [hlength]

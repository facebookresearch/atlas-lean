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

-- The empty initial state has no legal move.
example : ∀ t, ¬ AccelZeckMove (Finsupp.single 1 0) t := by
  simpa using not_accelZeckMove_zero

example : ¬ ∃ g : ℕ → ℕ →₀ ℕ, g 0 = 0 ∧ ∀ j, AccelZeckMove (g j) (g (j + 1)) := by
  rintro ⟨g, hstart, hmove⟩
  exact not_accelZeckMove_zero (g 1) (by simpa only [hstart] using hmove 0)

example : (0 : ℕ →₀ ℕ) = zeckendorfState 0 ∧ (0 : ℝ) ≤ 0 := by
  simpa using (accelZeckGame_terminates_at_zeckendorf 0).2 0 (fun _ => 0) isAccelZeckGame_zero

-- Three C₁ steps are batched into one turn. Then S₂, C₂, and S₃ are each played once.
private noncomputable def sixTokenPlay : ℕ → ℕ →₀ ℕ
  | 0 => Finsupp.single 1 6
  | 1 => Finsupp.single 2 3
  | 2 => Finsupp.single 1 1 + Finsupp.single 2 1 + Finsupp.single 3 1
  | 3 => Finsupp.single 3 2
  | _ => Finsupp.single 1 1 + Finsupp.single 4 1

private theorem sixTokenPlay_complete : IsAccelZeckGame 6 4 sixTokenPlay := by
  apply isAccelZeckGame_iff.mpr
  refine ⟨rfl, ?_, ?_⟩
  · intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj' with rfl | rfl | rfl | rfl
    · apply accelZeckMove_iff.mpr
      refine ⟨3, by decide, Or.inr (Or.inl ⟨by simp [sixTokenPlay], ?_⟩)⟩
      simp [sixTokenPlay]
    · apply accelZeckMove_iff.mpr
      refine ⟨1, by decide, Or.inr (Or.inr (Or.inl ⟨by simp [sixTokenPlay], ?_⟩))⟩
      ext i
      simp only [sixTokenPlay, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs <;> omega
    · apply accelZeckMove_iff.mpr
      refine ⟨1, by decide, Or.inl
        ⟨2, by decide, by simp [sixTokenPlay], by simp [sixTokenPlay], ?_⟩⟩
      ext i
      simp only [sixTokenPlay, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs <;> omega
    · apply accelZeckMove_iff.mpr
      refine ⟨1, by decide, Or.inr (Or.inr (Or.inr ⟨3, by decide, by simp [sixTokenPlay], ?_⟩))⟩
      simp [sixTokenPlay]
  · intro t h
    obtain ⟨m, hm, h⟩ := accelZeckMove_iff.mp h
    rcases h with ⟨i, hi, h₁, h₂, _⟩ | ⟨h₁, _⟩ | ⟨h₂, _⟩ | ⟨i, hi, hᵢ, _⟩
    · simp only [sixTokenPlay, Finsupp.add_apply, Finsupp.single_apply] at h₁ h₂
      split_ifs at h₁ h₂ <;> omega
    · simp [sixTokenPlay] at h₁
      omega
    · simp [sixTokenPlay] at h₂
      omega
    · simp only [sixTokenPlay, Finsupp.add_apply, Finsupp.single_apply] at hᵢ
      split_ifs at hᵢ <;> omega

-- This concrete play ends at F₁ + F₄. Its length satisfies the bound with index sum 5
-- and two summands in the decomposition of 6.
example : zeckendorfState 6 = Finsupp.single 1 1 + Finsupp.single 4 1 ∧
    (4 : ℝ) ≤ 3 + 2 * Real.sqrt 5 := by
  obtain ⟨hfinal, hlength⟩ :=
    (accelZeckGame_terminates_at_zeckendorf 6).2 4 sixTokenPlay sixTokenPlay_complete
  refine ⟨hfinal.symm, ?_⟩
  have hrep : ([5, 2] : List ℕ).IsZeckendorfRep := by simp [List.IsZeckendorfRep.eq_def]
  have hzeck := Nat.zeckendorf_sum_fib hrep
  rw [show ([5, 2].map Nat.fib).sum = 6 by decide] at hzeck
  rw [hzeck] at hlength
  change (4 : ℝ) ≤ (Real.sqrt 5 + 3) / 2 * 6 - 5 - (1 + Real.sqrt 5) / 2 * 2 at hlength
  linarith only [hlength]

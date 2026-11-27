/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.JosephusThreeHighExtremalSuccCases

open MetaMathlibExt

namespace JosephusThreeHighExtremalSuccCasesTest

private instance decidableHighExtremal : DecidablePred IsJosephusThreeHighExtremal :=
  fun n => inferInstanceAs (Decidable (1 ≤ n ∧ (josephus 3 n = n ∨ josephus 3 n + 1 = n)))

local notation "highAt" => Nat.nth IsJosephusThreeHighExtremal

-- The even pure point 8 is followed by the fixed point 13.
example : highAt 5 = 13 ∧ highAt 5 - josephus 3 (highAt 5) = 0 := by
  have ha : highAt 4 = 8 := Nat.nth_count (p := IsJosephusThreeHighExtremal) (n := 8) (by decide)
  have h := (josephusThree_highExtremal_succ_cases 4).1
  rw [ha] at h
  obtain ⟨hb, hf⟩ := h (by decide) (by decide)
  change 2 * highAt 5 = 26 at hb
  exact ⟨by omega, hf⟩

-- The odd pure point 3 is followed by the pure point 5.
example : highAt 3 = 5 ∧ highAt 3 - josephus 3 (highAt 3) = 1 := by
  have ha : highAt 2 = 3 := Nat.nth_count (p := IsJosephusThreeHighExtremal) (n := 3) (by decide)
  have h := (josephusThree_highExtremal_succ_cases 2).2.1
  rw [ha] at h
  obtain ⟨hb, hf⟩ := h (by decide) (by decide)
  change 2 * highAt 3 = 10 at hb
  exact ⟨by omega, hf⟩

-- The even fixed point 2 is followed by the pure point 3.
example : highAt 2 = 3 ∧ highAt 2 - josephus 3 (highAt 2) = 1 := by
  have ha : highAt 1 = 2 := Nat.nth_count (p := IsJosephusThreeHighExtremal) (n := 2) (by decide)
  have h := (josephusThree_highExtremal_succ_cases 1).2.2.1
  rw [ha] at h
  obtain ⟨hb, hf⟩ := h (by decide) (by decide)
  change 2 * highAt 2 = 6 at hb
  exact ⟨by omega, hf⟩

-- The odd fixed point 1 is followed by the fixed point 2.
example : highAt 1 = 2 ∧ highAt 1 - josephus 3 (highAt 1) = 0 := by
  have ha : highAt 0 = 1 := Nat.nth_count (p := IsJosephusThreeHighExtremal) (n := 1) (by decide)
  have h := (josephusThree_highExtremal_succ_cases 0).2.2.2
  rw [ha] at h
  obtain ⟨hb, hf⟩ := h (by decide) (by decide)
  change 2 * highAt 1 = 4 at hb
  exact ⟨by omega, hf⟩

end JosephusThreeHighExtremalSuccCasesTest

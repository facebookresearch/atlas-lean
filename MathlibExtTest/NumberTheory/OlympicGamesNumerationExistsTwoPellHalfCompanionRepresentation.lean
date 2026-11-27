/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.OlympicGamesNumerationExistsTwoPellHalfCompanionRepresentation

/-!
# Tests for mixed Pell numeration

The representation of nine has three copies of the three-place, zero units, and zero digits
in both neighboring odd places, including the place above the finite sum.
-/

namespace MathlibExtTest.NumberTheory.OlympicGamesNumerationExistsTwoPellHalfCompanionRepresentation

open Finset MetaMathlibExt

private lemma pell_sequences_monotone : Monotone pellNumber ∧ Monotone pellLucasSequence := by
  constructor
  · apply monotone_nat_of_le_succ
    intro n
    cases n with
    | zero => decide
    | succ n =>
      change pellNumber (n + 1) ≤ 2 * pellNumber (n + 1) + pellNumber n
      omega
  · apply monotone_nat_of_le_succ
    intro n
    cases n with
    | zero => decide
    | succ n =>
      change pellLucasSequence (n + 1) ≤
        2 * pellLucasSequence (n + 1) + pellLucasSequence n
      omega

example : ∃ a : ℕ → ℕ,
    9 = ∑ k ∈ range 3,
      a k * (if k % 2 = 1 then 2 * pellNumber k else pellLucasSequence k) ∧
    (a 0, a 1, a 2, a 3) = (0, 0, 3, 0) := by
  let R (k : ℕ) := if k % 2 = 1 then 2 * pellNumber k else pellLucasSequence k
  obtain ⟨n, a, hlo, hhi, hsum, h₀, hunit, hbound, hneighbors, _, _⟩ :=
    exists_two_pell_halfCompanion_representation R (fun _ ↦ rfl) (t := 9) (by decide)
  have hn : n ≤ 2 := by
    by_contra! h
    dsimp [R] at hlo
    split at hlo
    · have hp := pell_sequences_monotone.1 (show 3 ≤ n by omega)
      norm_num [pellNumber] at hp
      omega
    · have hh := pell_sequences_monotone.2 (show 4 ≤ n by omega)
      norm_num [pellLucasSequence] at hh
      omega
  obtain rfl : n = 2 := by
    rcases (show n = 0 ∨ n = 1 ∨ n = 2 by omega) with h | h | h
    · subst n
      norm_num [R, pellNumber, pellLucasSequence] at hhi
    · subst n
      norm_num [R, pellNumber, pellLucasSequence] at hhi
    · exact h
  refine ⟨a, hsum, ?_⟩
  have hb₁ := (hbound 0).2
  have hb₂ := (hbound 1).1
  simp only [Nat.mul_zero, Nat.zero_add] at hb₁
  simp only [Nat.mul_one] at hb₂
  simp [sum_range_succ, R, pellNumber, pellLucasSequence] at hsum
  have h₂ : a 2 = 3 := by omega
  have hodd : a 1 = 0 ∧ a 3 = 0 := by simpa using hneighbors 1 (by decide) h₂
  simp only [Prod.mk.injEq]
  omega

end MathlibExtTest.NumberTheory.OlympicGamesNumerationExistsTwoPellHalfCompanionRepresentation

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ExtendedContinuantOneSilentTerms
import Mathlib.Tactic.NormNum

/-!
# Tests for terms of a $1$-silent sequence

The identically zero sequences satisfy the strict-equivalence hypotheses, so `oneSilent_terms`
applies to them; sample indices check the three conclusions.
-/

@[expose] public section

namespace MathlibExtTest.NumberTheory.ExtendedContinuantOneSilentTerms

open MetaMathlibExt

/-- Continuants of the zero sequence step down by two in the order. -/
private theorem zero_step (a b : ℤ) :
    extendedContinuant (fun _ => 0) a b = extendedContinuant (fun _ => 0) (a - 2) b := by
  have h := extendedContinuant_recurrence (fun _ => 0) a b
  simpa using h

/-- The zero sequences satisfy the westbound strict-equivalence hypotheses. -/
private theorem zero_west : ∀ i : ℕ,
    extendedContinuant (fun _ => 0) (-(i : ℤ) - 2) 0 =
      extendedContinuant (fun _ => 0) i 0 ∧
    extendedContinuant (fun _ => 0) (-(i : ℤ) - 3) 1 =
      extendedContinuant (fun _ => 0) ((i : ℤ) - 1) 1 := by
  intro i
  induction i using Nat.twoStepInduction with
  | zero =>
    have c1 : (-((0 : ℕ) : ℤ) - 2) = -2 := by omega
    have c2 : (-((0 : ℕ) : ℤ) - 3) = -3 := by omega
    have c3 : (((0 : ℕ) : ℤ) - 1) = -1 := by omega
    rw [c1, c2, c3, Nat.cast_zero]
    constructor
    · rw [extendedContinuant_neg_two, extendedContinuant_zero]
    · rw [(extendedContinuant_neg_three_to_six _ _).1, extendedContinuant_neg_one]
  | one =>
    have c1 : (-((1 : ℕ) : ℤ) - 2) = -3 := by omega
    have c2 : (-((1 : ℕ) : ℤ) - 3) = -4 := by omega
    have c3 : (((1 : ℕ) : ℤ) - 1) = 0 := by omega
    have c4 : (((1 : ℕ) : ℤ)) = 1 := by omega
    rw [c1, c2, c3, c4]
    constructor
    · have z1 := zero_step 1 0
      norm_num at z1
      rw [extendedContinuant_neg_one] at z1
      rw [(extendedContinuant_neg_three_to_six _ _).1, z1]
    · have h4 := (extendedContinuant_neg_three_to_six (fun _ => 0) 1).2.1
      have h0 := extendedContinuant_zero (fun _ => 0) 1
      rw [h4, h0]
      simp
  | more n ih0 _ =>
    have eL : (-((n + 2 : ℕ) : ℤ) - 2) = (-(n : ℤ) - 2) - 2 := by omega
    have eR : (((n + 2 : ℕ) : ℤ)) = (n : ℤ) + 2 := by omega
    have eR2 : ((n : ℤ) + 2 - 2) = (n : ℤ) := by omega
    have eL' : (-((n + 2 : ℕ) : ℤ) - 3) = (-(n : ℤ) - 3) - 2 := by omega
    have eR' : (((n + 2 : ℕ) : ℤ) - 1) = ((n : ℤ) - 1) + 2 := by omega
    have eR2' : ((n : ℤ) - 1 + 2 - 2) = (n : ℤ) - 1 := by omega
    constructor
    · rw [eL, eR, ← zero_step (-(n : ℤ) - 2) 0, zero_step ((n : ℤ) + 2) 0, eR2]
      exact ih0.1
    · rw [eL', eR', ← zero_step (-(n : ℤ) - 3) 1, zero_step ((n : ℤ) - 1 + 2) 1, eR2']
      exact ih0.2

-- Eastbound agreement holds at index 7 for the zero sequences.
example : (fun _ => 0 : ℤ → ℤ) 7 = (fun _ => 0 : ℤ → ℤ) 7 :=
  (oneSilent_terms _ _ _ (fun _ => ⟨rfl, rfl⟩) zero_west).1 7

-- Westbound sign agreement holds at index 3 for the zero sequences.
example : (fun _ => 0 : ℤ → ℤ) (-3) = -((fun _ => 0 : ℤ → ℤ) 3) :=
  (oneSilent_terms _ _ _ (fun _ => ⟨rfl, rfl⟩) zero_west).2.1 3 (by decide)

-- The middle term vanishes for the zero westbound sequence.
example : (fun _ => 0 : ℤ → ℤ) 0 = 0 :=
  (oneSilent_terms _ _ _ (fun _ => ⟨rfl, rfl⟩) zero_west).2.2

end MathlibExtTest.NumberTheory.ExtendedContinuantOneSilentTerms

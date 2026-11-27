/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import MathlibExt.NumberTheory.ComplementarySequencesInterleaveFar

/-!
# Tests for the large-gap interleaving formula
-/

open MetaMathlibExt

namespace MathlibExtTest.NumberTheory.ComplementarySequencesInterleaveFar

private def squareSeq (m : ℕ) : ℕ := m * m
private def squareInterleave (m : ℕ) : ℝ := squareSeq (m - 1)
private def squareRank (n : ℕ) : ℕ := Nat.sqrt n + 1

private theorem square_formula (n : ℕ) (hn : 1 ≤ n) :
    nthNonValue squareSeq n =
      if squareSeq (squareRank n) < n + squareRank n then n + squareRank n
      else n + squareRank n - 1 := by
  apply nthNonValue_eq_interleave_of_le_sub squareSeq (by decide) _ squareInterleave _ squareRank
    _ _ n hn
  · intro m _
    unfold squareSeq
    nlinarith
  · intro m _
    refine ⟨le_rfl, ?_⟩
    unfold squareInterleave squareSeq
    exact_mod_cast Nat.mul_self_le_mul_self (Nat.sub_le m 1)
  · intro j _
    refine ⟨by simp [squareRank], ?_, ?_⟩
    · simp only [squareRank, squareInterleave, Nat.add_sub_cancel, squareSeq]
      exact_mod_cast Nat.sqrt_le j
    · simp only [squareRank, squareInterleave, Nat.add_sub_cancel, squareSeq]
      exact_mod_cast Nat.lt_succ_sqrt j
  · intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [squareInterleave, Nat.add_sub_cancel, squareSeq, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one]
    nlinarith only [Nat.cast_nonneg (α := ℝ) k]

-- At n = 1 the next square lies strictly above n + h(n).
example : nthNonValue squareSeq 1 = 2 := by
  rw [square_formula 1 (by decide)]
  decide

-- At n = 2 equality belongs to the n + h(n) - 1 branch.
example : nthNonValue squareSeq 2 = 3 := by
  have hs : Nat.sqrt 2 = 1 := (Nat.eq_sqrt'.mpr ⟨by decide, by decide⟩).symm
  rw [square_formula 2 (by decide), show squareRank 2 = 2 from congrArg (· + 1) hs]
  decide

-- At n = 3 the square 4 lies below n + h(n), and is skipped.
example : nthNonValue squareSeq 3 = 5 := by
  have hs : Nat.sqrt 3 = 1 := (Nat.eq_sqrt'.mpr ⟨by decide, by decide⟩).symm
  rw [square_formula 3 (by decide), show squareRank 3 = 2 from congrArg (· + 1) hs]
  decide

end MathlibExtTest.NumberTheory.ComplementarySequencesInterleaveFar

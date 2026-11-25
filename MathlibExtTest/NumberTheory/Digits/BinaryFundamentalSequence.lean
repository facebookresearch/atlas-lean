/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.BinaryFundamentalSequence

/-! # Tests for binary fundamental sequences -/

open MetaMathlibExt

-- The binary representation of zero is uniquely the empty set.
example (s : Finset ℕ) (hs : (∑ k ∈ s, 2 ^ k) = 0) : s = ∅ := by
  have h := (bijective_finset_sum_iff_eq_two_pow (H := fun k => 2 ^ k)
    Nat.two_pow_pos (fun _ _ h => Nat.pow_lt_pow_right (by decide) h)).2 (fun _ => rfl)
  exact h.injective (by simpa using hs)

-- The positive increasing sequence 1, 2, 3, … already fails at index two.
example : ¬ Function.Bijective (fun s : Finset ℕ => ∑ k ∈ s, (k + 1)) := by
  intro h
  have htwo := (bijective_finset_sum_iff_eq_two_pow (H := fun k => k + 1)
    (fun k => Nat.succ_pos k) (fun _ _ h => Nat.succ_lt_succ h)).1 h 2
  exact (by decide : (3 : ℕ) ≠ 4) htwo

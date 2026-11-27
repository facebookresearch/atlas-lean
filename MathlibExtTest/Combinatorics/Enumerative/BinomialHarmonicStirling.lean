/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.BinomialHarmonicStirling

open Finset MetaMathlibExt Complex

-- At exponent zero the k = 0 term survives, and only one Stirling term remains.
example (n : ℕ) (t : ℂ) (ht : ∀ m : ℤ, t ≠ m) :
    ∑ k ∈ range (n + 1), (-1 : ℂ) ^ k * Ring.choose t (n - k) *
        (digamma (t + 1) - digamma (t - n + k + 1)) =
      (-1) ^ n * (Ring.choose ((n : ℂ) - t) n *
        (digamma (-t + 1) - digamma (n - t + 1))) := by
  simpa using sum_choose_sub_harmonic_diff_stirling n 0 t ht

-- For n = 2 and r = 3, the truncated sum has a single nonzero term at k = 1.
example : ∑ k ∈ range 3, (-1 : ℂ) ^ k * Ring.choose I (2 - k) * (k : ℂ) ^ 3 *
    (digamma (I + 1) - digamma (I - 2 + k + 1)) = -1 := by
  have hI (m : ℤ) : I ≠ m := fun h => by simpa using congrArg im h
  have h := sum_choose_sub_harmonic_diff_stirling 2 3 I hI
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  norm_num [sum_range_succ, Nat.stirlingSecond, Ring.choose_one_right]
  have hp (m : ℕ) : 2 - I ≠ -(m : ℂ) := fun h => by simpa using congrArg im h
  rw [show 1 - I + 1 = 2 - I by ring, digamma_apply_add_one _ hp]
  have hn : 2 - I ≠ 0 := by simpa using hp 0
  field_simp
  ring

-- At exponent zero the dual identity has only the constant Stirling term.
example (n : ℕ) (t : ℂ) (ht : ∀ m : ℤ, t ≠ m) :
    ∑ k ∈ range (n + 1), (-1 : ℂ) ^ (n - k) * Ring.choose ((n : ℂ) - t) (n - k) *
        (digamma (k - t + 1) - digamma (n - t + 1)) =
      Ring.choose t n * (digamma (t + 1) - digamma (t - n + 1)) := by
  simpa using sum_choose_sub_harmonic_diff_stirling_dual n 0 t ht

-- Here r > n, and the term at k = 1 gives 1 by the digamma recurrence.
example : ∑ k ∈ range 3, (-1 : ℂ) ^ (2 - k) * Ring.choose (2 - I) (2 - k) * (k : ℂ) ^ 3 *
    (digamma (k - I + 1) - digamma (2 - I + 1)) = 1 := by
  have hI (m : ℤ) : I ≠ m := fun h => by simpa using congrArg im h
  have h := sum_choose_sub_harmonic_diff_stirling_dual 2 3 I hI
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  norm_num [sum_range_succ, Nat.stirlingSecond, Ring.choose_one_right]
  have hp (m : ℕ) : I ≠ -(m : ℂ) := fun h => by simpa using congrArg im h
  rw [show I - 2 + 1 + 1 = I by ring, digamma_apply_add_one _ hp]
  field_simp [Complex.I_ne_zero]
  ring

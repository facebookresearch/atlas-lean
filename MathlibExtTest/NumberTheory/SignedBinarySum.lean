/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SignedBinarySum

/-!
# Tests for signed binary sums
-/

namespace MetaMathlibExt

-- The negative integer -9 requires more than two signed powers.
example : ∃ k : ℕ, 1 ≤ k ∧ IsSignedPowTwoSum 1 1 k (-10) := by
  obtain ⟨k, hk, lam, hlam, hsum⟩ := (one_add_signedPowTwoSum_iff (-9)).mpr (by decide)
  exact ⟨k, hk, lam, hlam, by omega⟩

-- The empty sum gives zero, but no nonempty signed sum starting at exponent one does.
example : IsSignedPowTwoSum 1 1 0 0 :=
  ⟨fun _ => 1, by simp, by simp⟩

example (k : ℕ) (hk : 1 ≤ k) : ¬ IsSignedPowTwoSum 1 1 k 0 := by
  rintro ⟨lam, hlam, hsum⟩
  have h := (one_add_signedPowTwoSum_iff 1).mp ⟨k, hk, lam, hlam, by omega⟩
  exact (by decide : ¬ (1 : ℤ) ≡ 3 [ZMOD 4]) h

-- A single binary place realizes exactly the two endpoints.
example (n : ℤ) : IsSignedPowTwoSum 2 2 2 n ↔ n = -4 ∨ n = 8 := by
  rw [isSignedPowTwoSum_iff 2 2 2 (by decide) (by decide)]
  change (-4 ≤ n ∧ n ≤ 8 ∧ n % 12 = 8) ↔ _
  omega

-- On two places the interval is [-12, 24], with step 12.
example : IsSignedPowTwoSum 2 2 3 0 := by
  exact (isSignedPowTwoSum_iff 2 2 3 (by decide) (by decide) 0).mpr (by decide)

example : ¬ IsSignedPowTwoSum 2 2 3 4 := by
  rw [isSignedPowTwoSum_iff 2 2 3 (by decide) (by decide)]
  decide

-- Extending 5 · 2² to three places gives -2² + 5 · 2³ - 2⁴.
example : IsSignedPowTwoSum 5 2 4 20 := by
  refine isSignedPowTwoSum_extend 5 2 2 2 ?_ ?_ ?_ 20 ⟨fun _ => 5, by simp, by decide⟩ <;>
    decide +kernel

-- With odd m + 1, even an initially empty interval can extend to a nonempty sum for zero.
example : IsSignedPowTwoSum 2 1 2 0 := by
  refine isSignedPowTwoSum_extend 2 1 0 2 ?_ ?_ ?_ 0 ⟨fun _ => -1, by simp, by simp⟩ <;>
    decide +kernel

end MetaMathlibExt

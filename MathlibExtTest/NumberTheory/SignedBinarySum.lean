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

end MetaMathlibExt

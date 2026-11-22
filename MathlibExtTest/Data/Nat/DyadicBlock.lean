/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Data.Nat.DyadicBlock

open MetaMathlibExt

-- The first and last members of a block of width four have the same quotient.
example : 12 / 2 ^ 2 = 15 / 2 ^ 2 :=
  (div_two_pow_eq_iff_exists_block (i := 2) (by decide : 12 < 15)).mpr ⟨3, by decide, by decide⟩

-- Moving one step past the last member crosses the block boundary.
example : 15 / 2 ^ 2 ≠ 16 / 2 ^ 2 := by
  intro h
  obtain ⟨d, hlo, hhi⟩ := (div_two_pow_eq_iff_exists_block (by decide : 15 < 16)).mp h
  omega

-- At exponent zero each block contains just one natural number.
example {z z' : ℕ} (hz : z < z') : ¬ ∃ d : ℕ, d ≤ z ∧ z' < d + 1 := by
  simpa using mt (div_two_pow_eq_iff_exists_block (i := 0) hz).mpr (by simpa using Nat.ne_of_lt hz)

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ComplementarySequences

/-!
# Tests for complementary sequences
-/

open MetaMathlibExt

-- The identity sequence has empty positive complement.
example (n : ℕ) : nthNonValue id n = 0 := by
  apply Nat.nth_of_forall_not
  intro x _ ⟨hx, h⟩
  exact h x hx rfl

-- Equality at the threshold selects the last missing integer before the tetrahedral number 4.
example : nthNonValue (fun j => j * (j + 1) * (j + 2) / 6) 2 = 3 := by
  have h (j : ℕ) : (3 - 2) * j + 5 - 3 = j + 2 := by omega
  have result := nthNonValue_pyramidal_two_case_le_eight 3 (by decide) (by decide) 2 (by decide)
  change nthNonValue _ 2 = 3 at result
  simpa only [h] using result

-- At k = 8, the cube root changes from one to two just as the complement skips 9.
example : nthNonValue (fun j => j * (j + 1) * (6 * j + 5 - 8) / 6) 7 = 8 :=
  nthNonValue_pyramidal_two_case_le_eight 8 (by decide) (by decide) 7 (by decide)

example : nthNonValue (fun j => j * (j + 1) * (6 * j + 5 - 8) / 6) 8 = 10 :=
  nthNonValue_pyramidal_two_case_le_eight 8 (by decide) (by decide) 8 (by decide)

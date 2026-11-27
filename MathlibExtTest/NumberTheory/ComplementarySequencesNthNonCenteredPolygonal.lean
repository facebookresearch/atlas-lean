/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ComplementarySequencesNthNonCenteredPolygonal

/-!
# Tests for the non-centered polygonal numbers
-/

open MetaMathlibExt

namespace MathlibExtTest.NumberTheory.ComplementarySequencesNthNonCenteredPolygonal

-- With s = 0 the test passes and the term is n itself.
example : Nat.nth (fun x => ∀ j, 5 * j * (j + 1) / 2 + 1 ≠ x) (2 - 1) = 2 := by
  have hs : Nat.sqrt (2 * 2 / 5) = 0 :=
    (Nat.eq_sqrt'.mpr ⟨by decide, by decide⟩).symm
  simpa [hs] using nth_nonCenteredPolygonal 5 (by decide) 2 (by decide)

-- At n = 2 the centered triangle 4 is still ahead, so the term is 2.
example : Nat.nth (fun x => ∀ j, 3 * j * (j + 1) / 2 + 1 ≠ x) (2 - 1) = 2 := by
  have hs : Nat.sqrt (2 * 2 / 3) = 1 :=
    (Nat.eq_sqrt'.mpr ⟨by decide, by decide⟩).symm
  simpa [hs] using nth_nonCenteredPolygonal 3 (by decide) 2 (by decide)

-- At n = 4 the formula skips the centered triangle 4.
example : Nat.nth (fun x => ∀ j, 3 * j * (j + 1) / 2 + 1 ≠ x) (4 - 1) = 5 := by
  have hs : Nat.sqrt (2 * 4 / 3) = 1 :=
    (Nat.eq_sqrt'.mpr ⟨by decide, by decide⟩).symm
  simpa [hs] using nth_nonCenteredPolygonal 3 (by decide) 4 (by decide)

-- At n = 6 the root is 2 and the test fails, giving n + s - 1.
example : Nat.nth (fun x => ∀ j, 3 * j * (j + 1) / 2 + 1 ≠ x) (6 - 1) = 7 := by
  have hs : Nat.sqrt (2 * 6 / 3) = 2 :=
    (Nat.eq_sqrt'.mpr ⟨by decide, by decide⟩).symm
  simpa [hs] using nth_nonCenteredPolygonal 3 (by decide) 6 (by decide)

-- The centered squares skip 5 at n = 5.
example : Nat.nth (fun x => ∀ j, 4 * j * (j + 1) / 2 + 1 ≠ x) (5 - 1) = 6 := by
  have hs : Nat.sqrt (2 * 5 / 4) = 1 :=
    (Nat.eq_sqrt'.mpr ⟨by decide, by decide⟩).symm
  simpa [hs] using nth_nonCenteredPolygonal 4 (by decide) 5 (by decide)

end MathlibExtTest.NumberTheory.ComplementarySequencesNthNonCenteredPolygonal

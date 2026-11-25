/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CompoundSequence

/-! # Examples of deletions from compound sequences -/

namespace MetaMathlibExt.CompoundSequenceTest

-- For the sequence 1, 2, deleting the last term leaves a cofinite monoid.
-- Deleting the first leaves only the even numbers.
example (j : ℕ) (hj : j ≤ 1) :
    (AddSubmonoid.closure ((((Finset.range 2).erase j).image
      (compoundSequence 1 (fun _ ↦ 1) (fun _ ↦ 2))) : Set ℕ) : Set ℕ)ᶜ.Finite ↔ j = 1 := by
  apply (compoundSequence_erase_cofinite_iff 1 (by decide) (fun _ ↦ 1) (fun _ ↦ 2)
    (by decide) (by decide) j hj).trans
  simp
  omega

private def a (i : ℕ) := if i = 1 then 2 else 3
private def b (i : ℕ) := if i = 2 then 4 else 5

example : (List.range 4).map (compoundSequence 3 a b) = [18, 45, 60, 100] := by decide

-- Deleting 45 leaves a common factor of two.
-- Deleting 60 succeeds, even though each surviving pair has a common prime factor.
private abbrev remaining (j : ℕ) := ((Finset.range 4).erase j).image (compoundSequence 3 a b)

example : (AddSubmonoid.closure (remaining 1 : Set ℕ) : Set ℕ)ᶜ.Infinite :=
  (compoundSequence_erase_cofinite_iff 3 (by decide) a b (by decide) (by decide) 1
    (by decide)).not.mpr (by decide)

example : (AddSubmonoid.closure (remaining 2 : Set ℕ) : Set ℕ)ᶜ.Finite :=
  (compoundSequence_erase_cofinite_iff 3 (by decide) a b (by decide) (by decide) 2
    (by decide)).mpr (by decide)

end MetaMathlibExt.CompoundSequenceTest

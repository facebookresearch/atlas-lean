/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SZumkellerNotIsUnitarySZumkellerOfOdd

/-!
# Tests for no odd unitary s-Zumkeller numbers

An odd square and an odd residue class are not unitary s-Zumkeller.
-/

namespace MathlibExtTest.NumberTheory.SZumkellerNotIsUnitarySZumkellerOfOdd

open MetaMathlibExt

-- The odd square 9 is not unitary s-Zumkeller.
example : ¬ IsUnitarySZumkeller 9 :=
  not_isUnitarySZumkeller_of_odd 9 (by decide)

-- An entire odd residue class is excluded.
example (k : ℕ) : ¬ IsUnitarySZumkeller (2 * k + 1) :=
  not_isUnitarySZumkeller_of_odd _ ⟨k, rfl⟩

end MathlibExtTest.NumberTheory.SZumkellerNotIsUnitarySZumkellerOfOdd

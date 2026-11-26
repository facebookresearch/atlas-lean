/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SZumkellerSixDvdOfIsSZumkeller

/-! # Tests for `MathlibExt.NumberTheory.SZumkellerSixDvdOfIsSZumkeller` -/

namespace MathlibExtTest.NumberTheory.SZumkellerSixDvdOfIsSZumkeller

open MetaMathlibExt

-- 60 is s-Zumkeller and even, so 6 divides it.
example : 6 ∣ 60 :=
  six_dvd_of_isSZumkeller 60 isSZumkeller_sixty (by decide)

-- No number congruent to 2 mod 6 is s-Zumkeller.
example (k : ℕ) : ¬ IsSZumkeller (6 * k + 2) := by
  intro h
  have he : Even (6 * k + 2) := ⟨3 * k + 1, by omega⟩
  have h6 := six_dvd_of_isSZumkeller _ h he
  omega

end MathlibExtTest.NumberTheory.SZumkellerSixDvdOfIsSZumkeller

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SuperMZumkellerIsSuperMZumkellerOfIsKMPerfect

/-! # Tests for `k`-m-perfect implies super-m-Zumkeller with `4 ∣ k` -/

namespace MathlibExtTest.NumberTheory.SuperMZumkellerIsSuperMZumkellerOfIsKMPerfect

open MathlibExt.NumberTheory.SuperMZumkellerWanted

-- `128 = 2 ^ 7` is `4`-m-perfect, hence super-m-Zumkeller.
example : IsSuperMZumkeller 128 := by
  have h128 : IsKMPerfect 4 128 := by
    unfold IsKMPerfect
    decide
  exact isSuperMZumkeller_of_isKMPerfect 4 128 (by decide) (by decide) h128

-- `30 = 2 * 3 * 5` is `4`-m-perfect, hence super-m-Zumkeller.
example : IsSuperMZumkeller 30 := by
  have h30 : IsKMPerfect 4 30 := by
    unfold IsKMPerfect
    decide
  exact isSuperMZumkeller_of_isKMPerfect 4 30 (by decide) (by decide) h30

-- Every `4`-m-perfect number is super-m-Zumkeller.
example (n : ℕ) (h : IsKMPerfect 4 n) : IsSuperMZumkeller n :=
  isSuperMZumkeller_of_isKMPerfect 4 n (by decide) (by decide) h

end MathlibExtTest.NumberTheory.SuperMZumkellerIsSuperMZumkellerOfIsKMPerfect

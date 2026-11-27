/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HigherANumbersTowerTauAdjacentDigits

/-!
# Tests for the adjacent base-`p` digit criterion

The examples cover both cases of the criterion at `p = 5`, and the endpoint `i = 0`
at `p = 2`.
-/

namespace MathlibExtTest.NumberTheory.HigherANumbersTowerTauAdjacentDigits

open MetaMathlibExt

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

example : basePDigit 5 (towerTau 5 4 * 1) (-1) ≠ basePDigit 5 (towerTau 5 4 * 1) 0 :=
  mt (basePDigit_towerTau_neg_one_eq_zero_iff 5 4 (by decide) 1).mp (by decide)

example : basePDigit 5 (towerTau 5 4 * 5) (-1) = basePDigit 5 (towerTau 5 4 * 5) 0 :=
  (basePDigit_towerTau_neg_one_eq_zero_iff 5 4 (by decide) 5).mpr (dvd_refl 5)

example : basePDigit 2 (towerTau 2 1 * 0) (-1) = basePDigit 2 (towerTau 2 1 * 0) 0 :=
  (basePDigit_towerTau_neg_one_eq_zero_iff 2 1 (by decide) 0).mpr (dvd_zero 2)

end MathlibExtTest.NumberTheory.HigherANumbersTowerTauAdjacentDigits

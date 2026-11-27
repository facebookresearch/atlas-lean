/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.UnitarySpoofLehmerSpoofEvalLeOfIsSpoofLehmerSpoofOfBases

/-!
# Tests for the bound on unitary Lehmer factorizations
-/

namespace MathlibExtTest.NumberTheory.UnitarySpoofLehmerSpoofEvalLeOfIsSpoofLehmerSpoofOfBases

open MetaMathlibExt

-- The factorization 3·3 is a unitary 2-Lehmer factorization, so the bound applies to it.
example : spoofEval (spoofOfBases {3, 3}) ≤
    2 ^ 2 ^ Multiset.card {3, 3} - 2 ^ 2 ^ (Multiset.card {3, 3} - 1) :=
  spoofEval_le_of_isSpoofLehmer_spoofOfBases 2 {3, 3} (by
    rw [spoofOfBases_three_three]
    exact isSpoofLehmer_three_three)

-- On two factors the bound evaluates to 12.
example : spoofEval (spoofOfBases {3, 3}) ≤ 12 := by
  have hcard : Multiset.card ({3, 3} : Multiset ℕ) = 2 := by simp
  have hle := spoofEval_le_of_isSpoofLehmer_spoofOfBases 2 {3, 3} (by
    rw [spoofOfBases_three_three]
    exact isSpoofLehmer_three_three)
  have h12 : (2 : ℤ) ^ 2 ^ 2 - 2 ^ 2 ^ (2 - 1) = 12 := by norm_num
  rw [hcard, h12] at hle
  exact hle

end MathlibExtTest.NumberTheory.UnitarySpoofLehmerSpoofEvalLeOfIsSpoofLehmerSpoofOfBases

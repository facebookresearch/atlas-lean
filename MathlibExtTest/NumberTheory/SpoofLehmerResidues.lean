/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SpoofLehmerResidues
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

private theorem threeThree_not_trivial : ¬ IsTrivialSpoof (spoofOfBases {3, 3}) := by
  intro h
  have hm : (3, 1) ∈ spoofOfBases {3, 3} := by
    rw [spoofOfBases_three_three]
    simp
  have eq := h (3, 1) hm
  norm_num at eq

example : ¬ (3 : ℤ) ≡ 1 [ZMOD 3] := by
  have hL : IsSpoofLehmer 2 (spoofOfBases {3, 3}) := by
    rw [spoofOfBases_three_three]
    exact isSpoofLehmer_three_three
  have hdvd : (3 : ℤ) ∣ spoofEval (spoofOfBases {3, 3}) := by
    rw [spoofOfBases_three_three, spoofEval_spoofTotient_three_three.1]
    decide
  exact spoofLehmer_base_not_modEq_one {3, 3} 2 hL threeThree_not_trivial 3 hdvd
    (by norm_num [Int.isUnit_iff]) 3 (by simp)

example : (3 : ℤ) ≡ 1 [ZMOD 1] := by decide

end MetaMathlibExt

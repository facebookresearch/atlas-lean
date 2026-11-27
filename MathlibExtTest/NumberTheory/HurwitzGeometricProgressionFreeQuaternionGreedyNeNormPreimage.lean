/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HurwitzGeometricProgressionFreeQuaternionGreedyNeNormPreimage

/-!
# Tests for the quaternion greedy set and norm preimages

The quaternion greedy set cannot consist exactly of the Hurwitz units.
-/

namespace MathlibExtTest.NumberTheory.HurwitzGeometricProgressionFreeQuaternionGreedyNeNormPreimage

set_option quotPrecheck false in
local notation "𝐇" => Set.ofPred fun q : Quaternion ℚ =>
  (∃ a b c d : ℤ,
    q.re = (a : ℚ) ∧ q.imI = (b : ℚ) ∧ q.imJ = (c : ℚ) ∧ q.imK = (d : ℚ)) ∨
  (∃ a b c d : ℤ,
    q.re = (a : ℚ) + 1 / 2 ∧ q.imI = (b : ℚ) + 1 / 2 ∧
      q.imJ = (c : ℚ) + 1 / 2 ∧ q.imK = (d : ℚ) + 1 / 2)

set_option quotPrecheck false in
local notation "IsQuaternionGreedy" Gq:max => ∀ q : Quaternion ℚ, q ∈ Gq ↔
  (q ∈ 𝐇 ∧ q ≠ 0 ∧ ¬ ∃ a ∈ Gq, ∃ r ∈ 𝐇, r ≠ 0 ∧ Quaternion.normSq r ≠ 1 ∧
    a * r ∈ Gq ∧ q = a * r ^ 2)

example (Gq : Set (Quaternion ℚ)) (hGq : IsQuaternionGreedy Gq) :
    ¬ ∀ q : Quaternion ℚ, q ∈ Gq ↔ q ∈ 𝐇 ∧ Quaternion.normSq q = 1 := by
  intro h
  apply MetaMathlibExt.quaternionGreedy_ne_norm_preimage Gq hGq {1}
    (by simp)
  ext q
  simpa using h q

end MathlibExtTest.NumberTheory.HurwitzGeometricProgressionFreeQuaternionGreedyNeNormPreimage

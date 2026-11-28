/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MinFeaturesDefs

namespace MetaMathlibExt.Complexity.NPComplete.MinFeatures

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : MinFeaturesInstance) :
    minFeaturesDec (bitEncode i) = true ↔ WellFormed i ∧ MinFeaturesFeasible i := by
  simp [minFeaturesDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := MinFeaturesInstance) bits = none) :
    minFeaturesDec bits = false := by
  simp [minFeaturesDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : minFeaturesDec [true] = false :=
  rejects_undecodable [true] rfl

/-- When the target copies feature `0`, the single feature `0` is sufficient. -/
example :
    minFeaturesDec (bitEncode ((2, [([false, false], false), ([false, true], false),
      ([true, false], true), ([true, true], true)], 1) : MinFeaturesInstance)) = true := by
  apply (accepts_encoding _).2
  exact ⟨by unfold WellFormed; decide, {0}, rfl, by decide⟩

/-- When the target is the exclusive or of both features, no single feature is sufficient. -/
example :
    minFeaturesDec (bitEncode ((2, [([false, false], false), ([false, true], true),
      ([true, false], true), ([true, true], false)], 1) : MinFeaturesInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, S, hcard, hsuff⟩
  obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 hcard
  revert j hsuff
  decide

/-- An example with the wrong number of feature values is malformed. -/
example :
    minFeaturesDec (bitEncode ((2, [([false], false)], 0) : MinFeaturesInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨h, -⟩
  exact absurd (h ([false], false) (by simp)) (by decide)

end MetaMathlibExt.Complexity.NPComplete.MinFeatures

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.KFacilityLocationDefs

namespace MetaMathlibExt.Complexity.NPComplete.KFacilityLocation

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : KFacilityLocationInstance) :
    kFacilityLocationDec (bitEncode i) = true ↔
      WellFormed i ∧ KFacilityLocationFeasible i := by
  simp [kFacilityLocationDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := KFacilityLocationInstance) bits = none) :
    kFacilityLocationDec bits = false := by
  simp [kFacilityLocationDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : kFacilityLocationDec [true] = false :=
  rejects_undecodable [true] rfl

/-- With profits `[[3, 0], [0, 4]]`, the single facility `1` earns `0 + 4 = 4`. -/
example :
    kFacilityLocationDec (bitEncode
      (([[3, 0], [0, 4]], 1, 4) : KFacilityLocationInstance)) = true := by
  apply (accepts_encoding _).2
  exact ⟨by unfold WellFormed; decide, {1}, by decide, by unfold profit; decide⟩

/-- A single facility earns at most `4`, below the bound `5`. -/
example :
    kFacilityLocationDec (bitEncode
      (([[3, 0], [0, 4]], 1, 5) : KFacilityLocationInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, F, hcard, hprofit⟩
  obtain ⟨f, rfl⟩ := Finset.card_eq_one.1 hcard
  revert f hprofit
  unfold profit
  decide

/-- Opening both facilities earns `7`, so the bound `5` is met when `k = 2`. -/
example :
    kFacilityLocationDec (bitEncode
      (([[3, 0], [0, 4]], 2, 5) : KFacilityLocationInstance)) = true := by
  apply (accepts_encoding _).2
  exact ⟨by unfold WellFormed; decide, Finset.univ, by decide, by unfold profit; decide⟩

/-- A zero bound is malformed even though every facility set meets it. -/
example :
    kFacilityLocationDec (bitEncode
      (([[3, 0], [0, 4]], 0, 0) : KFacilityLocationInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨⟨-, h⟩, -⟩
  exact absurd h (by decide)

end MetaMathlibExt.Complexity.NPComplete.KFacilityLocation

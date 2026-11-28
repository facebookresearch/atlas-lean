/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.KFacilityDispersionDefs

namespace MetaMathlibExt.Complexity.NPComplete.KFacilityDispersion

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open KCenter (KCenterInstance)
open MetricKCenter (distance)

private theorem accepts_encoding (i : KCenterInstance) :
    kFacilityDispersionDec (bitEncode i) = true ↔
      WellFormed i ∧ KFacilityDispersionFeasible i := by
  simp [kFacilityDispersionDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := KCenterInstance) bits = none) :
    kFacilityDispersionDec bits = false := by
  simp [kFacilityDispersionDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : kFacilityDispersionDec [true] = false :=
  rejects_undecodable [true] rfl

/-- On the path metric `0 - 1 - 2`, the endpoints are two facilities at distance `2`. -/
example :
    kFacilityDispersionDec (bitEncode
      (([[0, 1, 2], [1, 0, 1], [2, 1, 0]], 2, 2) : KCenterInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨⟨by unfold MetricKCenter.WellFormed KCenter.WellFormed distance; decide,
    by decide⟩, {0, 2}, by decide, ?_⟩
  decide

/-- No two vertices of the path metric `0 - 1 - 2` are at distance `3`. -/
example :
    kFacilityDispersionDec (bitEncode
      (([[0, 1, 2], [1, 0, 1], [2, 1, 0]], 2, 3) : KCenterInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, F, hcard, hdist⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by rw [hcard]; decide)
  have hle : ∀ x y : Fin 3,
      distance (([[0, 1, 2], [1, 0, 1], [2, 1, 0]], 2, 3) : KCenterInstance) x y ≤ 2 := by
    unfold distance; decide
  have := hdist a ha b hb hab
  have := hle a b
  simp only at *
  omega

/-- A single facility (`k = 1`) is malformed for dispersion though metric k-center allows it. -/
example :
    kFacilityDispersionDec (bitEncode
      (([[0, 1, 2], [1, 0, 1], [2, 1, 0]], 1, 1) : KCenterInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨⟨-, h⟩, -⟩
  exact absurd h (by decide)

end MetaMathlibExt.Complexity.NPComplete.KFacilityDispersion

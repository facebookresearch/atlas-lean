/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MinimumAreaPolygonalizationDefs

namespace MetaMathlibExt.Complexity.NPComplete.MinimumAreaPolygonalization

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : MinimumAreaPolygonalizationInstance) :
    minimumAreaPolygonalizationDec (bitEncode i) = true ↔
      WellFormed i ∧ MinimumAreaPolygonalizationFeasible i := by
  simp [minimumAreaPolygonalizationDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : minimumAreaPolygonalizationDec [true] = false := by
  have h : bitDecode (α := MinimumAreaPolygonalizationInstance) [true] = none := rfl
  simp [minimumAreaPolygonalizationDec, h]

/-- A single point with area bound one decodes to a well-formed instance, but cannot form a
simple polygon. -/
example :
    let i : MinimumAreaPolygonalizationInstance := ([((0, 0), (0, 0))], ((1, 0), 1))
    bitDecode (bitEncode i) = some i ∧ WellFormed i ∧
      minimumAreaPolygonalizationDec (bitEncode i) = false := by
  dsimp only
  refine ⟨bitDecode_bitEncode _, ⟨?_, by decide⟩, ?_⟩
  · intro a b _
    apply Fin.ext
    have ha : a.val < 1 := a.isLt
    have hb : b.val < 1 := b.isLt
    omega
  · cases h : minimumAreaPolygonalizationDec
        (bitEncode (([((0, 0), (0, 0))], ((1, 0), 1)) : MinimumAreaPolygonalizationInstance)) with
    | false => rfl
    | true =>
      obtain ⟨_, _, hSimple, _⟩ := (accepts_encoding _).1 h
      exact ((by decide : ¬ (3 : Nat) ≤ 1) hSimple.1).elim

/-- A zero denominator is malformed even though the instance has a valid bitstring encoding. -/
example : minimumAreaPolygonalizationDec
    (bitEncode (([((0, 0), (0, 0))], ((1, 0), 0)) : MinimumAreaPolygonalizationInstance)) =
      false := by
  have h : ¬ WellFormed (([((0, 0), (0, 0))], ((1, 0), 0)) :
      MinimumAreaPolygonalizationInstance) := fun h => (by decide : ¬ 0 < (0 : Nat)) h.2
  simp [minimumAreaPolygonalizationDec, bitDecode_bitEncode, h]

end MetaMathlibExt.Complexity.NPComplete.MinimumAreaPolygonalization

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SideEffectFreeDeletionPropagationDefs

namespace MetaMathlibExt.Complexity.NPComplete.SideEffectFreeDeletionPropagation

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open Cslib.Databases

private theorem accepts_encoding (i : SideEffectFreeDeletionPropagationInstance) :
    sideEffectFreeDeletionPropagationDec (bitEncode i) = true ↔
      WellFormed i ∧ SideEffectFreeDeletionPropagationFeasible i := by
  simp [sideEffectFreeDeletionPropagationDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : sideEffectFreeDeletionPropagationDec [true] = false := by
  have h : bitDecode (α := SideEffectFreeDeletionPropagationInstance) [true] = none := rfl
  simp [sideEffectFreeDeletionPropagationDec, h]

/-- `R₁ = {(0, 0), (1, 0)}`, `R₂ = {(0, 0)}`: the view is `{(0, 0), (1, 0)}`, and deleting
`(0, 0)` from `R₁` removes exactly the view tuple `(0, 0)`. -/
example : sideEffectFreeDeletionPropagationDec
    (bitEncode (([(0, 0), (1, 0)], [(0, 0)], (0, 0)) :
      SideEffectFreeDeletionPropagationInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide,
    {pairTuple 0 1 0 0}, by decide, ∅, by decide, by decide⟩

/-- `R₁ = {(0, 0), (1, 0)}`, `R₂ = {(0, 0), (0, 1)}`: the view is all four pairs over `{0, 1}`.
Deleting `(0, 0)` from `R₁` also removes `(0, 1)`, and deleting `(0, 0)` from `R₂` also removes
`(1, 0)`, so no deletion is side-effect free for the view tuple `(0, 0)`. -/
example : sideEffectFreeDeletionPropagationDec
    (bitEncode (([(0, 0), (1, 0)], [(0, 0), (0, 1)], (0, 0)) :
      SideEffectFreeDeletionPropagationInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, T₁, hT₁, T₂, hT₂, heq⟩ := (accepts_encoding _).1 h
  rw [← Finset.mem_powerset] at hT₁ hT₂
  revert T₁ T₂
  decide

/-- A view tuple outside the view makes the instance malformed. -/
example : sideEffectFreeDeletionPropagationDec
    (bitEncode (([(0, 0)], [(0, 0)], (1, 1)) : SideEffectFreeDeletionPropagationInstance)) =
      false := by
  rw [Bool.eq_false_iff]
  intro h
  exact absurd ((accepts_encoding _).1 h).1.2.2 (by decide)

end MetaMathlibExt.Complexity.NPComplete.SideEffectFreeDeletionPropagation

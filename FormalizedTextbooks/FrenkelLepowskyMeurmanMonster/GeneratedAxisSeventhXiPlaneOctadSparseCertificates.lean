/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneOctadSparseData

/-! Exact sparse indices, genuine descriptors, and original central coefficients. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- All 552 original source descriptors and central coefficients are checked.
/-- Sparse rank and slot retain every original signed-octad shape
and its genuine preferred-Q sign. -/
theorem generatedSeventhXiOctad_source : ∀ r : Fin 552,
    let a := generatedSeventhXiOddSource r
    if generatedSeventhXiShortDescriptor a.1 a.2 0 = 1 then
      ∃ hg : generatedSeventhXiOctadRank r < 231,
      ∃ hk : generatedSeventhXiOctadSlot r < 3,
        generatedSeventhXiOctadEntries ⟨generatedSeventhXiOctadRank r, hg⟩
            ⟨generatedSeventhXiOctadSlot r, hk⟩ = r.val ∧
        generatedSeventhXiOctadCodes ⟨generatedSeventhXiOctadRank r, hg⟩ =
          generatedSeventhXiShortDescriptor a.1 a.2 1 ∧
        generatedSeventhXiOctadSigns ⟨generatedSeventhXiOctadRank r, hg⟩
            ⟨generatedSeventhXiOctadSlot r, hk⟩ = generatedSeventhXiShortDescriptor a.1 a.2 2 ∧
        generatedSeventhXiOctadWeights ⟨generatedSeventhXiOctadRank r, hg⟩
            ⟨generatedSeventhXiOctadSlot r, hk⟩ =
          generatedSeventhXiShortInputWeight a.1 a.2 *
            nortonUIntegerSign (generatedSeventhXiShortPhaseBit a.1 a.2 : ZMod 2)
    else generatedSeventhXiOctadRank r = 231 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Only three possible entries occur in each of the 231 original code rows.
/-- Every actual sparse entry has the stated source, and all absent slots have zero coefficient. -/
theorem generatedSeventhXiOctad_entry : ∀ g : Fin 231, ∀ k : Fin 3,
    if h : generatedSeventhXiOctadEntries g k < 552 then
      let r : Fin 552 := ⟨generatedSeventhXiOctadEntries g k, h⟩
      let a := generatedSeventhXiOddSource r
      generatedSeventhXiOctadRank r = g.val ∧ generatedSeventhXiOctadSlot r = k.val ∧
        generatedSeventhXiShortDescriptor a.1 a.2 0 = 1 ∧
        generatedSeventhXiOctadCodes g = generatedSeventhXiShortDescriptor a.1 a.2 1 ∧
        generatedSeventhXiOctadSigns g k = generatedSeventhXiShortDescriptor a.1 a.2 2 ∧
        generatedSeventhXiOctadWeights g k =
          generatedSeventhXiShortInputWeight a.1 a.2 *
            nortonUIntegerSign (generatedSeventhXiShortPhaseBit a.1 a.2 : ZMod 2)
    else generatedSeventhXiOctadEntries g k = 552 ∧ generatedSeventhXiOctadWeights g k = 0 := by
  decide +kernel

/-- Every occurring family has a genuine first original source. -/
theorem generatedSeventhXiOctad_first : ∀ g : Fin 231,
    generatedSeventhXiOctadEntries g 0 < 552 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

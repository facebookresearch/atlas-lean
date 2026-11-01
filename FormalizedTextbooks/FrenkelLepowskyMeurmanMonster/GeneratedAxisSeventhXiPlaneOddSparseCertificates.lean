/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneOddSparseData

/-! Exact sparse indices, genuine descriptors, and original central coefficients. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- All 552 original source descriptors and central coefficients are checked.
/-- The sparse rank and slot retain every actual original odd shape and its preferred-Q sign. -/
theorem generatedSeventhXiOdd_source : ∀ r : Fin 552,
    let a := generatedSeventhXiOddSource r
    if generatedSeventhXiShortDescriptor a.1 a.2 0 ≠ 0 ∧
        generatedSeventhXiShortDescriptor a.1 a.2 0 ≠ 1 then
      ∃ hg : generatedSeventhXiOddRank r < 232,
      ∃ hk : generatedSeventhXiOddSlot r < 3,
        generatedSeventhXiOddEntries ⟨generatedSeventhXiOddRank r, hg⟩
            ⟨generatedSeventhXiOddSlot r, hk⟩ = r.val ∧
        generatedSeventhXiOddCodes ⟨generatedSeventhXiOddRank r, hg⟩ =
          generatedSeventhXiShortDescriptor a.1 a.2 1 ∧
        generatedSeventhXiOddPositions ⟨generatedSeventhXiOddRank r, hg⟩
            ⟨generatedSeventhXiOddSlot r, hk⟩ = generatedSeventhXiShortDescriptor a.1 a.2 2 ∧
        generatedSeventhXiOddWeights ⟨generatedSeventhXiOddRank r, hg⟩
            ⟨generatedSeventhXiOddSlot r, hk⟩ =
          generatedSeventhXiShortInputWeight a.1 a.2 *
            nortonUIntegerSign (generatedSeventhXiShortPhaseBit a.1 a.2 : ZMod 2)
    else generatedSeventhXiOddRank r = 232 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Only three possible entries occur in each of the 232 original code rows.
/-- Every actual sparse entry has the stated source, and all absent slots have zero coefficient. -/
theorem generatedSeventhXiOdd_entry : ∀ g : Fin 232, ∀ k : Fin 3,
    if h : generatedSeventhXiOddEntries g k < 552 then
      let r : Fin 552 := ⟨generatedSeventhXiOddEntries g k, h⟩
      let a := generatedSeventhXiOddSource r
      generatedSeventhXiOddRank r = g.val ∧ generatedSeventhXiOddSlot r = k.val ∧
        generatedSeventhXiShortDescriptor a.1 a.2 0 ≠ 0 ∧
        generatedSeventhXiShortDescriptor a.1 a.2 0 ≠ 1 ∧
        generatedSeventhXiOddCodes g = generatedSeventhXiShortDescriptor a.1 a.2 1 ∧
        generatedSeventhXiOddPositions g k = generatedSeventhXiShortDescriptor a.1 a.2 2 ∧
        generatedSeventhXiOddWeights g k =
          generatedSeventhXiShortInputWeight a.1 a.2 *
            nortonUIntegerSign (generatedSeventhXiShortPhaseBit a.1 a.2 : ZMod 2)
    else generatedSeventhXiOddEntries g k = 552 ∧ generatedSeventhXiOddWeights g k = 0 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

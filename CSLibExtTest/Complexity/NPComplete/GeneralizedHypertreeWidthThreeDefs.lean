/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.GeneralizedHypertreeWidthThreeDefs

namespace MetaMathlibExt.Complexity.NPComplete.GeneralizedHypertreeWidthThree

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : GeneralizedHypertreeWidthThreeInstance) :
    generalizedHypertreeWidthThreeDec (bitEncode i) = true ↔
      WellFormed i ∧ GeneralizedHypertreeWidthThreeFeasible i := by
  simp [generalizedHypertreeWidthThreeDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : generalizedHypertreeWidthThreeDec [true] = false := by
  have h : bitDecode (α := GeneralizedHypertreeWidthThreeInstance) [true] = none := rfl
  simp [generalizedHypertreeWidthThreeDec, h]

/-- The path hypergraph on five vertices with edges `{0, 1}`, `{1, 2}`, `{2, 3}` and `{3, 4}`. -/
private abbrev path₅ : GeneralizedHypertreeWidthThreeInstance :=
  (5, [[0, 1], [1, 2], [2, 3], [3, 4]])

/-- A one-node decomposition: the single bag holds all five vertices, which the three edges
`{0, 1}`, `{1, 2}` and `{3, 4}` cover. -/
example : generalizedHypertreeWidthThreeDec (bitEncode path₅) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, 1, ⊥, fun _ => Finset.univ,
    fun _ => {0, 1, 3}, .of_subsingleton, fun _ => ⟨0, Finset.subset_univ _⟩,
    fun _ u v => Subsingleton.elim u v ▸ .refl _, ?_, ?_⟩
  · unfold edgeSet
    decide
  · decide

/-- No two of the four edges cover all five vertices: one bag needs three edges. -/
example : ∀ Λ : Finset (Fin path₅.2.length), Λ.card ≤ 2 →
    ¬ Finset.univ ⊆ Λ.biUnion (edgeSet path₅) := by
  unfold edgeSet
  decide

/-- A hyperedge naming vertex `5` in a hypergraph on three vertices is malformed. -/
example : generalizedHypertreeWidthThreeDec
    (bitEncode ((3, [[0, 5]]) : GeneralizedHypertreeWidthThreeInstance)) = false := by
  have h : ¬ WellFormed ((3, [[0, 5]]) : GeneralizedHypertreeWidthThreeInstance) := by
    unfold WellFormed
    decide
  simp [generalizedHypertreeWidthThreeDec, bitDecode_bitEncode, h]

end MetaMathlibExt.Complexity.NPComplete.GeneralizedHypertreeWidthThree

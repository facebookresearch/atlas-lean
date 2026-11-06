/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2TriangleRange

/-! The seventh matrix's actual triangle is an intrinsic A2 plane of its genuine octad section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Preferred labels of the original triangle roots genuinely lie in the seventh section. -/
theorem leechSeventhTriangle_label_supported (j : Fin 3) :
    leechSeventhE8RootLabel (leechSeventhE8A2Indices 537 j) ∈
      generatedAxisE8ShortLines
        (generatedAxisE8CoordinateSection (golayOctadWord generatedSeventhSectionOctad)) := by
  change griessShortLatticeVector (leechSeventhE8RootLabel (leechSeventhE8A2Indices 537 j)) ∈
    generatedAxisE8CoordinateSection (golayOctadWord generatedSeventhSectionOctad)
  rcases leechSeventhE8Root_label_sign (leechSeventhE8A2Indices 537 j) with h | h
  · rw [← h]
    exact leechSeventhE8A2_triangle_supported j
  · rw [← Submodule.neg_mem_iff, ← h]
    exact leechSeventhE8A2_triangle_supported j

/-- The actual seventh triangle plane belongs to the genuine intrinsic section-plane carrier. -/
theorem leechSeventhTriangle_intrinsic :
    leechSeventhE8A2Plane 537 ∈ leechSeventhA2PlanesIn
      (generatedAxisE8CoordinateSection (golayOctadWord generatedSeventhSectionOctad)) := by
  refine ⟨leechSeventhE8RootLabel (leechSeventhE8A2Indices 537 0),
    leechSeventhE8RootLabel (leechSeventhE8A2Indices 537 1),
    leechSeventhTriangle_label_supported 0, leechSeventhTriangle_label_supported 1,
    (leechSeventhE8Root_pairing_iff _ _).mp (leechSeventhE8A2_first_pair 537), ?_⟩
  exact (leechSeventhE8A2Plane_span_pair 537 0 1 (by decide)).trans
    (leechSeventh_span_pair_sign _ _ _ _
      (leechSeventhE8RealRoot_label_sign _) (leechSeventhE8RealRoot_label_sign _))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

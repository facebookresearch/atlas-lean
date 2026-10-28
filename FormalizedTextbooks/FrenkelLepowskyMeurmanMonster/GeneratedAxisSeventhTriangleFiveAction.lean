/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhTriangleFiveTransitivity

/-! Genuine triangle permutations preserve precisely the five complementary physical positions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false

private theorem five_as_complement (i : Fin 24) :
    i ∈ generatedSeventhFiveFrameCoordinates ↔
      golayOctadWord generatedSeventhSectionOctad i ≠ 0 ∧
        i ∉ generatedSeventhTriangleCoordinates := by
  rw [golayOctadWord, generatedSeventh_section_octad_label]
  simp_rw [golayLabelEncoder_boolean]
  revert i
  unfold generatedSeventhFiveFrameCoordinates generatedSeventhTriangleCoordinates
  decide +kernel

/-- The inverse of every genuine triangle permutation preserves the five literal positions. -/
theorem generatedSeventh_triangle_five_inverse_mem
    (p : generatedSeventhTrianglePermutationSubgroup) (i : Fin 24) :
    p.val.val.symm i ∈ generatedSeventhFiveFrameCoordinates ↔
      i ∈ generatedSeventhFiveFrameCoordinates := by
  obtain ⟨ho, ht⟩ := generatedSeventh_triangle_permutation_preserves p.val p.property
  have hw := congrFun ho i
  change golayOctadWord generatedSeventhSectionOctad (p.val.val.symm i) =
    golayOctadWord generatedSeventhSectionOctad i at hw
  have htri : p.val.val.symm i ∈ generatedSeventhTriangleCoordinates ↔
      i ∈ generatedSeventhTriangleCoordinates := by
    have h := Finset.smul_mem_smul_finset_iff p.val
      (b := p.val.val.symm i) (s := generatedSeventhTriangleCoordinates)
    rw [ht] at h
    simpa only [show p.val • p.val.val.symm i = i from p.val.val.apply_symm_apply i] using h.symm
  rw [five_as_complement, five_as_complement, hw, htri]

/-- Every genuine triangle permutation also preserves the five positions
in the forward direction. -/
theorem generatedSeventh_triangle_five_mem
    (p : generatedSeventhTrianglePermutationSubgroup) (i : Fin 24) :
    p.val.val i ∈ generatedSeventhFiveFrameCoordinates ↔
      i ∈ generatedSeventhFiveFrameCoordinates := by
  simpa only [Equiv.symm_apply_apply] using
    (generatedSeventh_triangle_five_inverse_mem p (p.val.val i)).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

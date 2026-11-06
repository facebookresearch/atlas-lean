/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8Co1StabilizerCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadProjectedLift

/-! The actual octad-axis stabilizer surjects onto the actual Co1 section stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual triality image of a signed short axis on the selected octad. -/
def generatedOctadLocalAxis (e : Fin 64) (c : ZMod 2) : GriessSpace :=
  sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedOctadBasisOctad, e))) c)

/-- Its genuine local stabilizer inside H. -/
def generatedOctadLocalAxisStabilizer (e : Fin 64) (c : ZMod 2) : Subgroup H :=
  MulAction.stabilizer H (generatedOctadLocalAxis e c)

/-- The literal coordinate projection is the actual octad-image matrix. -/
theorem generatedOctad_section_projection_eq_matrix (e : Fin 64) (c : ZMod 2) :
    Matrix.diagonal (fun i => if golayOctadWord generatedOctadBasisOctad i = 0
      then (0 : ℝ) else 1) = (griessConwayEncode (generatedOctadLocalAxis e c)).1 := by
  rw [generatedOctadLocalAxis, generatedAxis_triality_octad_matrix]
  congr 1
  funext i
  have hi : golayOctadWord generatedOctadBasisOctad i ≠ 0 ↔
      (golayEncodedMask (golayOctadLabel generatedOctadBasisOctad).val).testBit i.val = true := by
    simpa only [golayOctadSupport, golayMaskSupport, Finset.mem_filter,
      Finset.mem_univ, true_and] using golayOctadWord_ne_zero_iff generatedOctadBasisOctad i
  by_cases hb : (golayEncodedMask
      (golayOctadLabel generatedOctadBasisOctad).val).testBit i.val = true
  · simp [hb, hi.mpr hb]
  · have hz : golayOctadWord generatedOctadBasisOctad i = 0 := by
      by_contra hn
      exact hb (hi.mp hn)
    simp [hz, hb]

/-- Every actual axis-fixing local lift stabilizes the actual integral section spatially. -/
theorem generatedOctad_axis_stabilizer_spatial (e : Fin 64) (c : ZMod 2)
    (f : localFiberSubgroup)
    (hf : rhoLocal (localFiberIntoH f) (generatedOctadLocalAxis e c) =
      generatedOctadLocalAxis e c) :
    f.val.2 ∈ generatedAxisE8SectionStabilizer (golayOctadWord generatedOctadBasisOctad) := by
  rw [generatedAxisE8SectionStabilizer_mem]
  apply (generatedAxisE8_matrix_action_iff_section_stabilizer _ _).mp
  rw [generatedOctad_section_projection_eq_matrix e c]
  have h := congrArg (fun x : GriessSpace => (griessConwayEncode x).1) hf
  change (griessConwayEncode (localGriessRepresentation f _)).1 = _ at h
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply] at h
  exact h

/-- The restricted actual local projection takes values in the actual section-stabilizer image. -/
def generatedOctadLocalAxisProjection (e : Fin 64) (c : ZMod 2) :
    generatedOctadLocalAxisStabilizer e c →*
      generatedAxisE8Co1SectionStabilizer (golayOctadWord generatedOctadBasisOctad) :=
  (projH.comp (generatedOctadLocalAxisStabilizer e c).subtype).codRestrict _ (by
    intro h
    obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
    change localFiberIntoH f = h.val at hf
    have hfix : rhoLocal (localFiberIntoH f) (generatedOctadLocalAxis e c) =
        generatedOctadLocalAxis e c := by rw [hf]; exact h.property
    refine ⟨f.val.2, generatedOctad_axis_stabilizer_spatial e c f hfix, ?_⟩
    change QuotientGroup.mk' signsSubgroup f.val.2 = projH h.val
    rw [← hf]
    rfl)

/-- Genuine section-stabilizer lifts prove the restricted local projection is onto. -/
theorem generatedOctadLocalAxisProjection_surjective (e : Fin 64) (c : ZMod 2) :
    Function.Surjective (generatedOctadLocalAxisProjection e c) := by
  intro a
  obtain ⟨g, hg, hga⟩ := a.property
  obtain ⟨f, hfg, hfix⟩ := generatedOctad_projected_stabilizer_lift e c g
    ((generatedAxisE8SectionStabilizer_mem _ g).mp hg)
  refine ⟨⟨localFiberIntoH f, hfix⟩, Subtype.ext ?_⟩
  change projH (localFiberIntoH f) = a.val
  change QuotientGroup.mk' signsSubgroup f.val.2 = a.val
  rw [hfg]
  exact hga

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

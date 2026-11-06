/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadLocalCoordinates

/-! Every actual local lift of a coordinate-section stabilizer admits an actual
Q correction fixing the original triality octad axis. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every section-preserving genuine local lift can be corrected in Q to fix the octad axis.
Neither a root-system recognition theorem nor an orbit cardinality is an input. -/
theorem generatedOctad_local_lift_phase_correction (e : Fin 64) (c : ZMod 2)
    (f : localFiberSubgroup)
    (hg : generatedAxisE8ImageSection f.val.2 (golayOctadWord generatedOctadBasisOctad) =
      generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad)) :
    ∃ q : Q, rhoLocal (inclQ q * localFiberIntoH f)
      (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedOctadBasisOctad, e))) c)) =
      sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedOctadBasisOctad, e))) c) := by
  let x := sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedOctadBasisOctad, e))) c)
  let y := localGriessRepresentation f x
  have hpres := generatedAxisE8_preserves_of_image_eq _ f.val.2 hg
  have hm : (griessConwayEncode x).1 = (griessConwayEncode y).1 := by
    dsimp only [y]
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
    exact (generatedAxisE8_octad_stabilizer_axis_matrix
      generatedOctadBasisOctad e c f.val.2 hg).symm
  have hix : griessProd x x = (64 : ℝ) • x :=
    generatedAxis_triality_short_square _ c
  have hiy : griessProd y y = (64 : ℝ) • y := by
    dsimp only [y]
    rw [← localGriessRepresentation_product, hix, map_smul]
  obtain ⟨q, hq⟩ := generatedOctad_idempotents_Q_related x y hm
    (generatedAxis_triality_octad_tensor_zero_all generatedOctadBasisOctad e c)
    (generatedOctad_local_image_tensor_zero generatedOctadBasisOctad e c f)
    (generatedAxis_triality_octad_supported_square generatedOctadBasisOctad e c)
    (generatedOctad_local_image_supported_square generatedOctadBasisOctad e c f hpres)
    (generatedAxis_triality_octad_unsupported_zero generatedOctadBasisOctad e c)
    (generatedOctad_local_image_unsupported_zero generatedOctadBasisOctad e c f hpres)
    (generatedAxisE8_supported_pairing_four generatedOctadBasisOctad e c)
    (generatedAxis_raw_idempotent_short x hix)
    (generatedAxis_raw_idempotent_short y hiy)
  refine ⟨q⁻¹, ?_⟩
  change rhoLocal (inclQ q⁻¹ * localFiberIntoH f) x = x
  rw [map_mul]
  change rhoLocal (inclQ q⁻¹) y = x
  rw [← hq, map_inv, map_inv]
  exact (rhoLocal (inclQ q)).symm_apply_apply x

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

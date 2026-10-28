/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineSpreadConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineMarkingLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitLower

/-! Actual whole-matrix and marking constraints embed into a genuine spread stabilizer.
The selected-section root-range invariant is an explicit hypothesis in this leaf. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false

/-- Genuine lattice isometries fixing both the actual matrix and the complete marking carrier. -/
def generatedNinthAffineMatrixMarkingStabilizer : Subgroup leechIsomSubgroup :=
  generatedNinthSpatialStabilizer ⊓
    generatedNinthCo1MarkingStabilizer.comap (QuotientGroup.mk' signsSubgroup)

/-- The actual spread415 stabilizer in the full original selected-section group. -/
def generatedNinthAffineDestinationStabilizer : Subgroup generatedAxisE8FrameSystemSectionGroup :=
  MulAction.stabilizer _ (generatedNinthSpreadActual 415)

/-- Direct reading of the original nine-state row is the existing actual spread415. -/
theorem generatedNinth_affine_destination_carrier_eq :
    generatedNinthAffineDestinationCarrier = generatedNinthSpreadActual 415 := by
  classical
  unfold generatedNinthAffineDestinationCarrier generatedNinthSpreadActual
    generatedNinthSpreadIndexSet
  rw [Finset.image_image]
  rfl

/-- An already reached actual spread has the same stabilizer size as the source spread. -/
theorem generatedNinth_affine_destination_stabilizer_card_le :
    Nat.card generatedNinthAffineDestinationStabilizer ≤ 185794560 := by
  obtain ⟨a, ha⟩ := generatedNinth_spread_actual_mem_orbit 415
  have hc := Nat.card_congr (MulAction.stabilizerEquivStabilizer ha.symm).toEquiv
  change Nat.card generatedNinthSpreadSectionStabilizer =
    Nat.card generatedNinthAffineDestinationStabilizer at hc
  rw [← hc]
  exact generatedNinth_spread_section_stabilizer_card_le

/-- Original-section root-range preservation supplies the full recovered-range invariant. -/
theorem generatedNinth_affine_spatial_root_preserved
    (hsection : ∀ a : generatedAxisE8FrameSystemSectionGroup,
      generatedAxisE8FrameRootEmbedding.range.map (leechModTwoAction a.val).toLinearMap =
        generatedAxisE8FrameRootEmbedding.range)
    (g : leechIsomSubgroup) (hg : g ∈ generatedNinthSpatialStabilizer) :
    generatedNinthAffineRootClassRange.map (leechModTwoAction g).toLinearMap =
      generatedNinthAffineRootClassRange := by
  apply generatedNinth_affine_root_preserved_of_conjugate
  exact hsection ⟨_, generatedNinth_affine_spatial_conjugate_mem_section g hg⟩

/-- Conjugation embeds the actual matrix-and-marking subgroup into the whole spread stabilizer. -/
def generatedNinthAffineConstraintHom
    (hsection : ∀ a : generatedAxisE8FrameSystemSectionGroup,
      generatedAxisE8FrameRootEmbedding.range.map (leechModTwoAction a.val).toLinearMap =
        generatedAxisE8FrameRootEmbedding.range) :
    generatedNinthAffineMatrixMarkingStabilizer →* generatedNinthAffineDestinationStabilizer where
  toFun g := ⟨⟨generatedNinthAffineTransport * g.val * generatedNinthAffineTransport⁻¹,
    generatedNinth_affine_spatial_conjugate_mem_section g.val g.property.1⟩,
      by
        change (generatedNinthAffineTransport * g.val * generatedNinthAffineTransport⁻¹) •
          generatedNinthSpreadActual 415 = generatedNinthSpreadActual 415
        simpa only [generatedNinth_affine_destination_carrier_eq] using
          generatedNinth_affine_spread_conjugate_fixed g.val
            (generatedNinth_affine_spatial_root_preserved hsection g.val g.property.1)
            (generatedNinth_affine_marking_lift_preserved g.val g.property.2)⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    simp [mul_assoc]

/-- The genuine conjugation homomorphism is injective on the entire actual subgroup. -/
theorem generatedNinth_affine_constraint_hom_injective
    (hsection : ∀ a : generatedAxisE8FrameSystemSectionGroup,
      generatedAxisE8FrameRootEmbedding.range.map (leechModTwoAction a.val).toLinearMap =
        generatedAxisE8FrameRootEmbedding.range) :
    Function.Injective (generatedNinthAffineConstraintHom hsection) := by
  intro a b h
  have hc := congrArg (fun k : generatedNinthAffineDestinationStabilizer =>
    generatedNinthAffineTransport⁻¹ * k.val.val * generatedNinthAffineTransport) h
  apply Subtype.ext
  change generatedNinthAffineTransport⁻¹ *
      (generatedNinthAffineTransport * a.val * generatedNinthAffineTransport⁻¹) *
        generatedNinthAffineTransport =
    generatedNinthAffineTransport⁻¹ *
      (generatedNinthAffineTransport * b.val * generatedNinthAffineTransport⁻¹) *
        generatedNinthAffineTransport at hc
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hc

/-- Both complete actual constraints limit the genuine Co0 subgroup to185794560 elements. -/
theorem generatedNinth_affine_matrix_marking_card_le
    (hsection : ∀ a : generatedAxisE8FrameSystemSectionGroup,
      generatedAxisE8FrameRootEmbedding.range.map (leechModTwoAction a.val).toLinearMap =
        generatedAxisE8FrameRootEmbedding.range) :
    Nat.card generatedNinthAffineMatrixMarkingStabilizer ≤ 185794560 := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  exact (Nat.card_le_card_of_injective (generatedNinthAffineConstraintHom hsection)
    (generatedNinth_affine_constraint_hom_injective hsection)).trans
      generatedNinth_affine_destination_stabilizer_card_le

/-- Both genuine central signs lie in the full matrix-and-marking constraint subgroup. -/
theorem generatedNinth_affine_signs_le_constraint :
    signsSubgroup ≤ generatedNinthAffineMatrixMarkingStabilizer := by
  intro g hg
  refine ⟨generatedNinth_signs_le_spatial hg, ?_⟩
  change QuotientGroup.mk' signsSubgroup g ∈ generatedNinthCo1MarkingStabilizer
  have he : QuotientGroup.mk' signsSubgroup g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
  rw [he]
  exact generatedNinthCo1MarkingStabilizer.one_mem

/-- Taking central-sign classes gives exactly the two genuine Conway constraints. -/
theorem generatedNinth_affine_constraint_map :
    generatedNinthAffineMatrixMarkingStabilizer.map (QuotientGroup.mk' signsSubgroup) =
      generatedNinthCo1SpatialStabilizer ⊓ generatedNinthCo1MarkingStabilizer := by
  ext c
  constructor
  · rintro ⟨g, ⟨hs, hm⟩, rfl⟩
    exact ⟨⟨g, hs, rfl⟩, hm⟩
  · rintro ⟨⟨g, hs, rfl⟩, hm⟩
    exact ⟨g, ⟨hs, hm⟩, rfl⟩

/-- Exactly two genuine lattice lifts occur above each actual Conway constraint. -/
theorem generatedNinth_affine_constraint_card_twice :
    2 * Nat.card ↥(generatedNinthCo1SpatialStabilizer ⊓
      generatedNinthCo1MarkingStabilizer) =
      Nat.card generatedNinthAffineMatrixMarkingStabilizer := by
  have hc := (signsSubgroup.subgroupOf generatedNinthAffineMatrixMarkingStabilizer).card_mul_index
  have hs := Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe generatedNinth_affine_signs_le_constraint).toEquiv
  rw [hs, signsSubgroup_card] at hc
  change 2 * signsSubgroup.relIndex generatedNinthAffineMatrixMarkingStabilizer = _ at hc
  have hi := Subgroup.relIndex_ker (K := generatedNinthAffineMatrixMarkingStabilizer)
    (QuotientGroup.mk' signsSubgroup)
  rw [QuotientGroup.ker_mk', generatedNinth_affine_constraint_map] at hi
  rw [hi] at hc
  exact hc

/-- The whole actual Conway matrix-and-marking subgroup has at most92897280 elements. -/
theorem generatedNinth_affine_co1_constraint_card_le
    (hsection : ∀ a : generatedAxisE8FrameSystemSectionGroup,
      generatedAxisE8FrameRootEmbedding.range.map (leechModTwoAction a.val).toLinearMap =
        generatedAxisE8FrameRootEmbedding.range) :
    Nat.card ↥(generatedNinthCo1SpatialStabilizer ⊓ generatedNinthCo1MarkingStabilizer) ≤
      92897280 := by
  have hu := generatedNinth_affine_matrix_marking_card_le hsection
  rw [← generatedNinth_affine_constraint_card_twice] at hu
  omega

/-- The actual full-axis Conway projection obeys the bound after exact octad comparison. -/
theorem generatedNinth_affine_projection_card_le_of_octad_comparison
    (hsection : ∀ a : generatedAxisE8FrameSystemSectionGroup,
      generatedAxisE8FrameRootEmbedding.range.map (leechModTwoAction a.val).toLinearMap =
        generatedAxisE8FrameRootEmbedding.range)
    (hoctad : ∀ (o : Fin 759) (e : Fin 64),
      |(griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inl (o, e)))| = 1 / 8 ↔
        o = 459 ∧ e ∈ generatedNinthOctadMarkedSigns) :
    Nat.card generatedNinthProjectedAxisStabilizer ≤ 92897280 := by
  let : Finite generatedNinthCo1SpatialStabilizer := Nat.finite_of_card_ne_zero
    (by rw [generatedNinthCo1SpatialStabilizer_card]; decide)
  let : Finite ↥(generatedNinthCo1SpatialStabilizer ⊓ generatedNinthCo1MarkingStabilizer) :=
    Finite.of_injective
      (Subgroup.inclusion (show generatedNinthCo1SpatialStabilizer ⊓
        generatedNinthCo1MarkingStabilizer ≤ generatedNinthCo1SpatialStabilizer from inf_le_left))
      (Subgroup.inclusion_injective _)
  have hl := generatedNinthProjectedAxisStabilizer_le_matrix_marking_of_octad_comparison hoctad
  exact (Nat.card_le_card_of_injective (Subgroup.inclusion hl)
    (Subgroup.inclusion_injective hl)).trans
      (generatedNinth_affine_co1_constraint_card_le hsection)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

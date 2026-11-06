/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMarkingSpatialTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLocalSpatialProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryFaithfulness

/-! The actual Ninth full-axis projection preserves its actual short marking classes.
The exact octad comparison remains explicit until its complete source replay is supplied.
The class carrier uses the genuine lattice quotient, without candidate packed tables. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Genuine hyperbolic coordinates of the144 candidate actual short lattice classes. -/
def generatedNinthMarkedBinaryClasses : Set (Fin 24 → ZMod 2) :=
  leechHyperbolicCoordinates '' generatedNinthMarkedShortClasses

/-- The actual Conway subgroup preserving the complete intrinsic marking-class carrier. -/
def generatedNinthCo1MarkingStabilizer : Subgroup Co1 where
  carrier := {g | co1BinaryAction g '' generatedNinthMarkedBinaryClasses =
    generatedNinthMarkedBinaryClasses}
  one_mem' := by
    change co1BinaryAction 1 '' generatedNinthMarkedBinaryClasses =
      generatedNinthMarkedBinaryClasses
    rw [map_one]
    exact Set.image_id _
  mul_mem' := by
    intro a b ha hb
    change co1BinaryAction a '' generatedNinthMarkedBinaryClasses =
      generatedNinthMarkedBinaryClasses at ha
    change co1BinaryAction b '' generatedNinthMarkedBinaryClasses =
      generatedNinthMarkedBinaryClasses at hb
    change co1BinaryAction (a * b) '' generatedNinthMarkedBinaryClasses =
      generatedNinthMarkedBinaryClasses
    rw [map_mul]
    change (co1BinaryAction a ∘ co1BinaryAction b) '' generatedNinthMarkedBinaryClasses = _
    rw [Set.image_comp, hb, ha]
  inv_mem' := by
    intro g hg
    change co1BinaryAction g '' generatedNinthMarkedBinaryClasses =
      generatedNinthMarkedBinaryClasses at hg
    change co1BinaryAction g⁻¹ '' generatedNinthMarkedBinaryClasses =
      generatedNinthMarkedBinaryClasses
    rw [map_inv]
    have hh := congrArg (fun s => (co1BinaryAction g).symm '' s) hg
    rw [Set.image_image] at hh
    simpa only [Function.comp_def, LinearEquiv.symm_apply_apply, Set.image_id',
      LinearEquiv.coe_inv] using hh.symm

/-- Every actual full-axis fixing fiber has its genuine Conway image in the marking subgroup,
once the exact original octad comparison has been supplied. -/
theorem generatedNinth_local_fiber_marking_image_of_octad_comparison
    (hoctad : ∀ (o : Fin 759) (e : Fin 64),
      |(griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inl (o, e)))| = 1 / 8 ↔
        o = 459 ∧ e ∈ generatedNinthOctadMarkedSigns)
    (f : localFiberSubgroup)
    (hfix : rhoLocal (localFiberIntoH f) generatedNinthAxis = generatedNinthAxis) :
    co1BinaryAction (projH (localFiberIntoH f)) '' generatedNinthMarkedBinaryClasses =
      generatedNinthMarkedBinaryClasses := by
  change leechBinaryAction f.val.2 '' generatedNinthMarkedBinaryClasses =
    generatedNinthMarkedBinaryClasses
  unfold generatedNinthMarkedBinaryClasses
  have hs := generatedNinth_fixed_marking_classes_image_of_octad_comparison hoctad f hfix
  ext w
  constructor
  · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
    rw [leechBinaryAction_coordinates]
    exact ⟨leechModTwoAction f.val.2 v,
      generatedNinth_fixed_marking_class_of_octad_comparison hoctad f hfix v hv, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    have hu' : u ∈ leechModTwoAction f.val.2 '' generatedNinthMarkedShortClasses := by
      rw [hs]
      exact hu
    obtain ⟨v, hv, hvu⟩ := hu'
    refine ⟨leechHyperbolicCoordinates v, ⟨v, hv, rfl⟩, ?_⟩
    rw [leechBinaryAction_coordinates, hvu]

/-- The actual full-axis projection lies in the actual Conway marking subgroup once the
exact original octad comparison has been supplied. -/
theorem generatedNinthProjectedAxisStabilizer_le_marking_of_octad_comparison
    (hoctad : ∀ (o : Fin 759) (e : Fin 64),
      |(griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inl (o, e)))| = 1 / 8 ↔
        o = 459 ∧ e ∈ generatedNinthOctadMarkedSigns) :
    generatedNinthProjectedAxisStabilizer ≤ generatedNinthCo1MarkingStabilizer := by
  rintro c ⟨h, rfl⟩
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH f = h.val at hf
  have hfix : rhoLocal (localFiberIntoH f) generatedNinthAxis = generatedNinthAxis := by
    rw [hf]
    exact h.property
  have hm := generatedNinth_local_fiber_marking_image_of_octad_comparison hoctad f hfix
  change projH h.val ∈ generatedNinthCo1MarkingStabilizer
  rw [← hf]
  exact hm

/-- Both the whole actual matrix and the complete intrinsic marking carrier constrain the
actual full-axis projection once the exact original octad comparison has been supplied. -/
theorem generatedNinthProjectedAxisStabilizer_le_matrix_marking_of_octad_comparison
    (hoctad : ∀ (o : Fin 759) (e : Fin 64),
      |(griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inl (o, e)))| = 1 / 8 ↔
        o = 459 ∧ e ∈ generatedNinthOctadMarkedSigns) :
    generatedNinthProjectedAxisStabilizer ≤
      generatedNinthCo1SpatialStabilizer ⊓ generatedNinthCo1MarkingStabilizer :=
  le_inf generatedNinthProjectedAxisStabilizer_le_spatial
    (generatedNinthProjectedAxisStabilizer_le_marking_of_octad_comparison hoctad)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

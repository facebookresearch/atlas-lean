/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingCoordinateSectionCatalogue

/-! Whole-axis phase fibers over the actual original 77 coordinate rooted E8 sections. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

private def preimageSigmaEquiv {X Y : Type*} (f : X → Y) (S : Set Y) :
    (f ⁻¹' S) ≃ Σ s : S, {x : X // f x = s.val} where
  toFun x := ⟨⟨f x.val, x.property⟩, ⟨x.val, rfl⟩⟩
  invFun x := ⟨x.2.val, by
    change f x.2.val ∈ S
    rw [x.2.property]
    exact x.1.property⟩
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨⟨s, hs⟩, x, hx⟩
    cases hx
    rfl

/-- All actual source A-orbit vectors lying over the original incident coordinate sections. -/
def generatedFeasibleContainingCoordinateSectionPhaseVectors :
    Set (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination) :=
  generatedFeasibleContainingCoordinateSourceSectionMap ⁻¹'
    generatedFeasibleContainingCoordinateIncidentRootedSections

/-- Every genuine original coordinate section contributes exactly 128 whole-axis phase vectors. -/
theorem generatedFeasibleContainingCoordinateSectionPhaseVectors_card :
    Nat.card generatedFeasibleContainingCoordinateSectionPhaseVectors = 9856 := by
  have : Finite generatedFeasibleContainingCoordinateIncidentRootedSections :=
    Nat.finite_of_card_ne_zero (by
      rw [generatedFeasibleContainingCoordinateIncidentRootedSections_card]
      decide)
  let := Fintype.ofFinite generatedFeasibleContainingCoordinateIncidentRootedSections
  have hf (S : generatedFeasibleContainingCoordinateIncidentRootedSections) :
      Finite {x // generatedFeasibleContainingCoordinateSourceSectionMap x = S.val} :=
    Nat.finite_of_card_ne_zero (by
      change Nat.card (generatedFeasibleContainingCoordinateSourceSectionMap ⁻¹' {S.val}) ≠ 0
      rw [generatedFeasibleContainingCoordinateSourceSectionMap_fiber_card]
      decide)
  rw [generatedFeasibleContainingCoordinateSectionPhaseVectors,
    Nat.card_congr (preimageSigmaEquiv _ _), Nat.card_sigma]
  have hc (S : generatedFeasibleContainingCoordinateIncidentRootedSections) :
      Nat.card {x // generatedFeasibleContainingCoordinateSourceSectionMap x = S.val} = 128 :=
    generatedFeasibleContainingCoordinateSourceSectionMap_fiber_card S.val
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, generatedFeasibleContainingCoordinateIncidentRootedSections_card]
  norm_num

/-- Any genuine monomial source lift gives a member of the actual 77-section catalogue. -/
theorem generatedFeasibleContainingCoordinateSourceSectionMap_catalogue
    (a : localAxisStabilizer generatedFeasiblePhysicalRootPair)
    (f : localFiberSubgroup) (hf : localFiberIntoH f = a.val)
    (hm : f.val.2 ∈ golayMonomialSubgroup) :
    generatedFeasibleContainingCoordinateSourceSectionMap
      ⟨rhoLocal a.val generatedFeasibleContainingOctadDestination, ⟨a, rfl⟩⟩ ∈
        generatedFeasibleContainingCoordinateIncidentRootedSections := by
  obtain ⟨p, hp⟩ := generatedFeasibleContainingCoordinateSourceSectionMap_monomial a f hf hm
  change (generatedFeasibleContainingCoordinateSourceSectionMap
    ⟨rhoLocal a.val generatedFeasibleContainingOctadDestination, ⟨a, rfl⟩⟩).val ∈
      generatedFeasibleContainingCoordinateIncidentSections
  rw [hp]
  apply generatedFeasibleContainingCoordinateIncidentSections_of_word
  · exact (p.property _).mp (golayOctadWord_mem_code _)
  · exact (Equiv.sum_comp p.val.symm
      (fun i => (golayOctadWord generatedOctadBasisOctad i).val)).trans
        (golayOctadWord_weight _)
  · have h := (generatedFeasibleContainingCoordinateSourceSectionMap
      ⟨rhoLocal a.val generatedFeasibleContainingOctadDestination, ⟨a, rfl⟩⟩).property.2
    rwa [hp] at h

/-- The actual underlying Griess vectors in all coordinate rooted-section phase fibers. -/
def generatedFeasibleContainingCoordinateActualPhaseAxes : Set GriessSpace :=
  Set.range (fun x : generatedFeasibleContainingCoordinateSectionPhaseVectors => x.val.val)

/-- Forgetting the two proof subtypes loses none of these genuine whole-axis vectors. -/
theorem generatedFeasibleContainingCoordinateActualPhaseAxes_card :
    Nat.card generatedFeasibleContainingCoordinateActualPhaseAxes = 9856 := by
  have hi : Function.Injective
      (fun x : generatedFeasibleContainingCoordinateSectionPhaseVectors => x.val.val) := by
    intro x y h
    exact Subtype.ext (Subtype.ext h)
  unfold generatedFeasibleContainingCoordinateActualPhaseAxes
  rw [← Nat.card_congr (Equiv.ofInjective _ hi)]
  exact generatedFeasibleContainingCoordinateSectionPhaseVectors_card

/-- An actual monomial spatial lift places its entire original source-axis image in these fibers.
-/
theorem generatedFeasibleContainingCoordinateActualPhaseAxes_word_mem
    (a : localAxisStabilizer generatedFeasiblePhysicalRootPair)
    (f : localFiberSubgroup) (hf : localFiberIntoH f = a.val)
    (hm : f.val.2 ∈ golayMonomialSubgroup) :
    rhoLocal a.val generatedFeasibleContainingOctadDestination ∈
      generatedFeasibleContainingCoordinateActualPhaseAxes := by
  refine ⟨⟨⟨rhoLocal a.val generatedFeasibleContainingOctadDestination, ⟨a, rfl⟩⟩, ?_⟩, rfl⟩
  exact generatedFeasibleContainingCoordinateSourceSectionMap_catalogue a f hf hm

/-- The genuine odd cocode reflector lies in the original first-root stabilizer. -/
def generatedFeasibleContainingCoordinateReflectionLocal :
    localAxisStabilizer generatedFeasiblePhysicalRootPair :=
  ⟨inclQ (cocodeQ generatedFeasibleContainingCoordinateReflection),
    generatedFeasibleContaining_odd_cocode_first_fixed _
      generatedFeasibleContainingCoordinateReflection_odd _⟩

/-- This actual Q word takes the whole original first prototype to the second prototype. -/
theorem generatedFeasibleContainingCoordinateReflectionLocal_image :
    rhoLocal generatedFeasibleContainingCoordinateReflectionLocal.val
      generatedFeasibleContainingOctadDestination = generatedFeasibleContainingTrialitySquare :=
  generatedFeasibleContaining_cocode_square_transport _
    generatedFeasibleContainingCoordinateReflection_odd _ _
      generatedFeasibleContainingCoordinateReflection_phase

/-- Every first-sector simultaneous image lies in a genuine original coordinate phase fiber. -/
theorem generatedFeasibleContainingCoordinateFirstNOrbit_subset_phases :
    generatedFeasibleContainingCoordinateNOrbit generatedFeasibleContainingOctadDestination ⊆
      generatedFeasibleContainingCoordinateActualPhaseAxes := by
  rintro x ⟨n, hn⟩
  change rhoLocal n.val generatedFeasibleContainingOctadDestination = x at hn
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup n.val
  change localFiberIntoH f = n.val at hf
  have hm := generatedFeasible_localOmega_lift_monomial f (hf.symm ▸ n.property.2)
  rw [← hn]
  exact generatedFeasibleContainingCoordinateActualPhaseAxes_word_mem
    ⟨n.val, n.property.1⟩ f hf hm

/-- Every second-sector simultaneous image lies in a genuine original coordinate phase fiber. -/
theorem generatedFeasibleContainingCoordinateSecondNOrbit_subset_phases :
    generatedFeasibleContainingCoordinateNOrbit generatedFeasibleContainingTrialitySquare ⊆
      generatedFeasibleContainingCoordinateActualPhaseAxes := by
  rintro x ⟨n, hn⟩
  change rhoLocal n.val generatedFeasibleContainingTrialitySquare = x at hn
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup n.val
  change localFiberIntoH f = n.val at hf
  have hm := generatedFeasible_localOmega_lift_monomial f (hf.symm ▸ n.property.2)
  let a : localAxisStabilizer generatedFeasiblePhysicalRootPair :=
    ⟨n.val, n.property.1⟩ * generatedFeasibleContainingCoordinateReflectionLocal
  let u : localFiberSubgroup :=
    f * localFiberIncl (cocodeQ generatedFeasibleContainingCoordinateReflection)
  have hu : localFiberIntoH u = a.val := by
    change localFiberIntoH (f * localFiberIncl
      (cocodeQ generatedFeasibleContainingCoordinateReflection)) =
        n.val * inclQ (cocodeQ generatedFeasibleContainingCoordinateReflection)
    rw [map_mul, hf]
    rfl
  have hum : u.val.2 ∈ golayMonomialSubgroup := by
    change f.val.2 * 1 ∈ golayMonomialSubgroup
    rwa [mul_one]
  have hi := generatedFeasibleContainingCoordinateActualPhaseAxes_word_mem a u hu hum
  have he : rhoLocal a.val generatedFeasibleContainingOctadDestination = x := by
    change rhoLocal (n.val * generatedFeasibleContainingCoordinateReflectionLocal.val)
      generatedFeasibleContainingOctadDestination = x
    rw [map_mul, LinearEquiv.mul_apply,
      generatedFeasibleContainingCoordinateReflectionLocal_image, hn]
  rwa [he] at hi

/-- The two proved coordinate N sectors exhaust every actual phase fiber over all 77 coordinate
rooted sections. This uses the genuine 128-fiber theorem and exact finite equality. -/
theorem generatedFeasibleContainingCoordinatePhaseSectors_eq_all_coordinate_phases :
    generatedFeasibleContainingCoordinatePhaseSectors =
      generatedFeasibleContainingCoordinateActualPhaseAxes := by
  have : Finite generatedFeasibleContainingCoordinateActualPhaseAxes :=
    Nat.finite_of_card_ne_zero (by
      rw [generatedFeasibleContainingCoordinateActualPhaseAxes_card]
      decide)
  apply Set.eq_of_subset_of_ncard_le
  · exact Set.union_subset generatedFeasibleContainingCoordinateFirstNOrbit_subset_phases
      generatedFeasibleContainingCoordinateSecondNOrbit_subset_phases
  · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
      generatedFeasibleContainingCoordinateActualPhaseAxes_card,
      generatedFeasibleContainingCoordinatePhaseSectors_card]
  · exact Set.toFinite _

/-- Above each of the 77 exact original encoder codes there are precisely 128 actual source axes. -/
theorem generatedFeasibleContainingCoordinateIncidentCode_phase_fiber_card
    (d : generatedFeasibleContainingCoordinateIncidentCodes) :
    Nat.card (generatedFeasibleContainingCoordinateSourceSectionMap ⁻¹'
      {generatedFeasibleContainingCoordinateIncidentCodeSection d}) = 128 :=
  generatedFeasibleContainingCoordinateSourceSectionMap_fiber_card _

/-- Coordinate-sector membership is equivalent to an actual rooted-section image named by an
original incident code, with the whole vector retained in the genuine containing A orbit. -/
theorem generatedFeasibleContainingCoordinatePhaseSectors_mem_iff (x : GriessSpace) :
    x ∈ generatedFeasibleContainingCoordinatePhaseSectors ↔
      ∃ hx : x ∈ MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
        generatedFeasibleContainingOctadDestination,
        ∃ d : generatedFeasibleContainingCoordinateIncidentCodes,
          (generatedFeasibleContainingCoordinateSourceSectionMap ⟨x, hx⟩).val =
            generatedAxisE8CoordinateSection (golayEncoder (golayLabelCoefficients d.val)) := by
  rw [generatedFeasibleContainingCoordinatePhaseSectors_eq_all_coordinate_phases]
  constructor
  · rintro ⟨y, hy⟩
    change y.val.val = x at hy
    have hp := y.property
    change (generatedFeasibleContainingCoordinateSourceSectionMap y.val).val ∈
      generatedFeasibleContainingCoordinateIncidentSections at hp
    obtain ⟨d, hd⟩ := hp
    refine ⟨hy ▸ y.val.property, d, ?_⟩
    have he : (⟨x, hy ▸ y.val.property⟩ :
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleContainingOctadDestination) = y.val := Subtype.ext hy.symm
    rw [he]
    exact hd.symm
  · rintro ⟨hx, d, hd⟩
    refine ⟨⟨⟨x, hx⟩, ?_⟩, rfl⟩
    change (generatedFeasibleContainingCoordinateSourceSectionMap ⟨x, hx⟩).val ∈
      generatedFeasibleContainingCoordinateIncidentSections
    refine ⟨d, ?_⟩
    exact hd.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroColumnCoverage
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOutsideOctadOrbitCount

/-! Complete containing-column coverage identifies any actual outside transition with the zero
class.
The genuine whole-axis outside transition is constructed separately; it is required here. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The established outside and secondary actual classes have distinct independently proved
orbits. -/
theorem generatedFeasibleContainingZeroOutsideAnchor_class_ne_secondary :
    generatedFeasibleSecondaryAClass generatedFeasibleOutsideOctadDestination ≠
      generatedFeasibleSecondaryAClass
        (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) := by
  intro he
  obtain ⟨h, hh⟩ := (generatedFeasibleSecondaryAClass_eq_iff _ _).mp he
  have hh' : h • generatedFeasibleOutsideOctadDestination =
      generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair := hh
  have hc := congrArg (fun S : Set GriessSpace => Nat.card S)
    (MulAction.orbit_smul h generatedFeasibleOutsideOctadDestination)
  have hS : Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)) = 93150 :=
    generatedFeasibleSecondaryLocalOrbit_card generatedFeasiblePhysicalRootPair
  rw [hh', generatedFeasibleOutsideOctad_actual_A_orbit_card, hS] at hc
  omega

/-- One realized entire outside transition is recognized by the already complete actual column.
No expected count or proposed classification is an input to this recognition. -/
theorem generatedFeasibleContainingZeroOutsideAnchor_class_of_actual_input
    (c : generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair)
    (hc : generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination c =
        generatedFeasibleSecondaryAClass generatedFeasibleOutsideOctadDestination) :
    generatedFeasibleSecondaryAClass generatedFeasibleContainingZeroDestination =
      generatedFeasibleSecondaryAClass generatedFeasibleOutsideOctadDestination := by
  obtain ⟨k, hk⟩ := generatedFeasibleContainingZeroColumnSources_coverage c
  have he := hk.symm.trans hc
  have hi := congrArg generatedFeasibleContainingAClassFirst he
  rw [generatedFeasibleContainingZeroColumnSources_first] at hi
  have hz : generatedFeasibleContainingAClassFirst
      (generatedFeasibleSecondaryAClass generatedFeasibleOutsideOctadDestination) = 0 :=
    generatedFeasibleContainingEstablishedDestinationSource_first 3
  rw [hz] at hi
  fin_cases k
  · norm_num at hi
  · exact False.elim (generatedFeasibleContainingZeroOutsideAnchor_class_ne_secondary he.symm)
  · exact he
  · norm_num at hi
  · norm_num at hi

/-- A genuine outside-to-containing pair of full first-axis words supplies an actual reverse
input. -/
theorem generatedFeasibleContainingZeroOutsideAnchor_class_of_actual_transition
    (k l : localAxisStabilizer generatedFeasiblePhysicalRootPair)
    (hkl : sExtra (rhoLocal k.val generatedFeasibleOutsideOctadDestination) =
      rhoLocal l.val generatedFeasibleContainingOctadDestination) :
    generatedFeasibleSecondaryAClass generatedFeasibleContainingZeroDestination =
      generatedFeasibleSecondaryAClass generatedFeasibleOutsideOctadDestination := by
  let x := rhoLocal k.val generatedFeasibleOutsideOctadDestination
  have hx : x ∈ generatedFeasibleTransitionVectors generatedFeasiblePhysicalRootPair
      generatedFeasibleOutsideOctadDestination generatedFeasibleContainingOctadDestination := by
    refine ⟨⟨k, rfl⟩, ?_⟩
    rw [hkl]
    exact ⟨l, rfl⟩
  have hy := generatedFeasibleTransition_reflection_mem generatedFeasiblePhysicalRootPair
    generatedFeasibleOutsideOctadDestination generatedFeasibleContainingOctadDestination x hx
  obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hy.1
  obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp hy.2
  change rhoLocal h.val generatedFeasibleContainingOctadDestination =
    generatedAxisTransitionReflection x at hh
  change rhoLocal a.val generatedFeasibleOutsideOctadDestination =
    sExtra (generatedAxisTransitionReflection x) at ha
  let c : generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair :=
    Quotient.mk (QuotientGroup.rightRel
      (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h
  apply generatedFeasibleContainingZeroOutsideAnchor_class_of_actual_input c
  change generatedFeasibleSecondaryAClass
    (sExtra (rhoLocal h.val generatedFeasibleContainingOctadDestination)) = _
  apply (generatedFeasibleSecondaryAClass_eq_iff _ _).mpr
  refine ⟨a⁻¹, ?_⟩
  rw [hh]
  exact generatedFeasibleContaining_inverse_transports a.val _ _ ha

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionReciprocity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFirstColumn
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisOctadOrbitCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisOddOrbitCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthFlagFramesExact

/-! Exact reverse transitions from the counted second, third and fourth actual axis orbits.
These are consequences of genuine transition reciprocity and the proved first column. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem generatedAxisTransition_start_orbit_card (p : Fin 276) :
    Nat.card (MulAction.orbit H (conwayAxis p)) = 196560 := by
  rw [generatedAxisLocalActual_orbit_eq_signed]
  exact generatedSignedShortAxes_card

private theorem generatedAxisTransition_octad_class (e : Fin 64) (c : ZMod 2) :
    Quotient.mk (MulAction.orbitRel H GriessSpace) (generatedOctadLocalAxis e c) =
      generatedAxisOctadDestination :=
  (generatedAxis_triality_octad_class_iff _ c).mpr ⟨generatedOctadBasisOctad, e, rfl⟩

/-- Exactly 135 actual transition cosets take any counted octad-image axis to the first H orbit. -/
theorem generatedAxisActualTransition_octad_to_first_card
    (p : Fin 276) (e : Fin 64) (c : ZMod 2) :
    Nat.card (generatedAxisActualTransitionCosets (generatedOctadLocalAxis e c) (conwayAxis p)) =
      135 := by
  have h := generatedAxisActualTransition_reciprocity (conwayAxis p) (generatedOctadLocalAxis e c)
  have hf : Nat.card (generatedAxisActualTransitionCosets (conwayAxis p)
      (generatedOctadLocalAxis e c)) = 8197200 := by
    rw [generatedAxisActualTransitionCosets_start, generatedAxisTransition_octad_class]
    exact generatedAxis_octad_transition_fiber_card p
  have ho : Nat.card (MulAction.orbit H (generatedOctadLocalAxis e c)) = 11935123200 :=
    generatedOctadLocalAxisOrbit_card e c
  rw [generatedAxisTransition_start_orbit_card, hf, ho] at h
  omega

/-- Exactly one actual transition coset takes the counted odd-image axis to the first H orbit. -/
theorem generatedAxisActualTransition_odd_to_first_card (p : Fin 276) :
    Nat.card (generatedAxisActualTransitionCosets generatedOddAxis (conwayAxis p)) = 1 := by
  have h := generatedAxisActualTransition_reciprocity (conwayAxis p) generatedOddAxis
  have hf : Nat.card (generatedAxisActualTransitionCosets (conwayAxis p) generatedOddAxis) =
      8294400 := by
    rw [generatedAxisActualTransitionCosets_start]
    exact generatedAxis_odd_transition_fiber_card p
  have ho : Nat.card (MulAction.orbit H generatedOddAxis) = 1630347264000 :=
    generatedOddLocalAxisOrbit_card
  rw [generatedAxisTransition_start_orbit_card, hf, ho] at h
  omega

private theorem generatedAxisTransition_class_ne_of_card_ne (a b : GriessSpace)
    (h : Nat.card (MulAction.orbit H a) ≠ Nat.card (MulAction.orbit H b)) :
    Quotient.mk (MulAction.orbitRel H GriessSpace) a ≠
      Quotient.mk (MulAction.orbitRel H GriessSpace) b := by
  intro he
  have hm := MulAction.orbitRel_apply.mp (Quotient.exact' he)
  have ho := MulAction.orbit_eq_iff.mpr hm
  exact h (congrArg (fun s : Set GriessSpace => Nat.card s) ho)

/-- No actual transition coset takes the first H orbit to the counted fourth H orbit. -/
theorem generatedAxisActualTransition_first_to_fourth_empty (p : Fin 276) :
    generatedAxisActualTransitionCosets (conwayAxis p) generatedFourthAxis = ∅ := by
  have hc := generatedFourthFlagFrames_axis_orbit_card
  have hn0 : Quotient.mk (MulAction.orbitRel H GriessSpace) generatedFourthAxis ≠
      Quotient.mk (MulAction.orbitRel H GriessSpace) (conwayAxis p) := by
    apply generatedAxisTransition_class_ne_of_card_ne
    rw [hc, generatedAxisTransition_start_orbit_card]
    decide
  have hn1 : Quotient.mk (MulAction.orbitRel H GriessSpace) generatedFourthAxis ≠
      generatedAxisOctadDestination := by
    rw [← generatedAxisTransition_octad_class 0 0]
    apply generatedAxisTransition_class_ne_of_card_ne
    rw [hc, show Nat.card (MulAction.orbit H (generatedOctadLocalAxis 0 0)) = 11935123200
      from generatedOctadLocalAxisOrbit_card 0 0]
    decide
  have hn2 : Quotient.mk (MulAction.orbitRel H GriessSpace) generatedFourthAxis ≠
      generatedAxisOddDestination := by
    change Quotient.mk (MulAction.orbitRel H GriessSpace) generatedFourthAxis ≠
      Quotient.mk (MulAction.orbitRel H GriessSpace) generatedOddAxis
    apply generatedAxisTransition_class_ne_of_card_ne
    rw [hc, show Nat.card (MulAction.orbit H generatedOddAxis) = 1630347264000
      from generatedOddLocalAxisOrbit_card]
    decide
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  rw [generatedAxisActualTransitionCosets_start] at hq
  have he : generatedAxisTransitionDestination p q =
      Quotient.mk (MulAction.orbitRel H GriessSpace) generatedFourthAxis := hq
  rcases generatedAxis_first_column_destinations p q with h0 | h1 | h2
  · exact hn0 (he.symm.trans h0)
  · exact hn1 (he.symm.trans h1)
  · exact hn2 (he.symm.trans h2)

/-- No actual transition coset takes the counted fourth H orbit to the first H orbit. -/
theorem generatedAxisActualTransition_fourth_to_first_card (p : Fin 276) :
    Nat.card (generatedAxisActualTransitionCosets generatedFourthAxis (conwayAxis p)) = 0 := by
  have h := generatedAxisActualTransition_reciprocity (conwayAxis p) generatedFourthAxis
  have he : Nat.card (∅ : Set generatedAxisTransitionCosetSpace) = 0 := Nat.card_of_isEmpty
  rw [generatedAxisActualTransition_first_to_fourth_empty, he,
    mul_zero, generatedFourthFlagFrames_axis_orbit_card] at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

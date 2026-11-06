/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingE7FrameNormalization

/-! Full original positive-first-root normalization of selected-square-sixteen projections. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

private theorem first_projection_pairing_zero (r : GriessShortIndex)
    (hP : griessShortIntegral r 0 = griessShortIntegral r 1) :
    (∑ i : Fin 24,
      (griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair))).val i *
        (generatedFeasibleContainingDoubledProjection (griessShortLatticeVector r)).val i) = 0 := by
  have hp (v : Fin 24 → ℤ) :
      (∑ i : Fin 24,
        griessShortIntegral (Sum.inl (0, generatedFeasiblePhysicalRootPair)) i * v i) =
          4 * (v 0 - v 1) := by
    simp only [griessShortIntegral, generatedFeasiblePhysicalRootPair_coordinates,
      ite_true, add_mul, mul_ite, ite_mul, mul_zero, zero_mul, mul_one,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  change (∑ i : Fin 24,
    griessShortIntegral (Sum.inl (0, generatedFeasiblePhysicalRootPair)) i *
      (generatedFeasibleContainingDoubledProjection (griessShortLatticeVector r)).val i) = 0
  rw [hp, generatedFeasibleContainingDoubledProjection_coordinate,
    generatedFeasibleContainingDoubledProjection_coordinate]
  change 4 * ((if (0 : ℕ) < 8 then 2 * griessShortIntegral r 0 else 0) -
    (if (1 : ℕ) < 8 then 2 * griessShortIntegral r 1 else 0)) = 0
  rw [if_pos (by decide : (0 : ℕ) < 8), if_pos (by decide : (1 : ℕ) < 8), hP]
  ring

/-- Every actual selected-square-sixteen projection normalizes to the third positive coordinate
frame, while retaining the entire source section and the positive original first root. -/
theorem generatedFeasibleContaining_selected_sixteen_projection_normalize
    (r : GriessShortIndex)
    (hS : generatedFeasibleContainingSelectedShortSquare r = 16)
    (hP : griessShortIntegral r 0 = griessShortIntegral r 1) :
    ∃ g : leechIsomSubgroup,
      generatedAxisE8ImageSection g
        (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) =
          generatedAxisE8CoordinateSection
            (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) ∧
      leechIntegralAction g
        (griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair))) =
          griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) ∧
      leechIntegralAction g
        (generatedFeasibleContainingDoubledProjection (griessShortLatticeVector r)) =
          leechCoordinateFrameLattice 2 := by
  let P := griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair))
  let u := generatedFeasibleContainingDoubledProjection (griessShortLatticeVector r)
  have hu : generatedOctadSupported golayStandardOctad u.val :=
    generatedFeasibleContainingDoubledProjection_section (griessShortLatticeVector r)
  have hn : leechSquareSum u.val = 64 := by
    have h := generatedFeasibleContainingDoubledProjection_square (griessShortLatticeVector r)
    change leechSquareSum u.val = 4 * generatedFeasibleContainingSelectedShortSquare r at h
    rw [hS] at h
    norm_num at h
    exact h
  have hf : generatedOctadSupported golayStandardOctad
      (leechCoordinateFrameLattice 2).val := by
    intro i hi
    have hn : i ≠ 2 := by
      intro h
      subst i
      norm_num [golayStandardOctad] at hi
    simp [leechCoordinateFrameLattice, leechCoordinateFrameVector, hn]
  obtain ⟨e, _, heS, heU⟩ := generatedOctad_normEight_transitive golayStandardOctad
    golayStandardOctad_mem golayStandardOctad_weight u (leechCoordinateFrameLattice 2)
      hu hf hn (leechCoordinateFrameVector_square 2)
  have heP : generatedStandardOctadSupported (leechIntegralAction e P).val := by
    apply (generatedOctadSupported_standard _).mp
    apply (heS P).mpr
    intro i hi
    have h0 : i ≠ 0 := by intro h; subst i; norm_num [golayStandardOctad] at hi
    have h1 : i ≠ 1 := by intro h; subst i; norm_num [golayStandardOctad] at hi
    simp [P, griessShortLatticeVector, griessShortIntegral,
      generatedFeasiblePhysicalRootPair_coordinates, h0, h1]
  have heN : leechSquareSum (leechIntegralAction e P).val = 32 := by
    rw [leechIntegralAction_squareSum]
    exact griessShortIntegral_squareSum (Sum.inl (0, generatedFeasiblePhysicalRootPair))
  have he2 : (leechIntegralAction e P).val 2 = 0 := by
    have h := generatedFeasibleContaining_integral_action_pairing e P u
    rw [heU, first_projection_pairing_zero r hP] at h
    change (∑ i : Fin 24, (leechIntegralAction e P).val i *
      (Pi.single (2 : Fin 24) (8 : ℤ) : Fin 24 → ℤ) i) = 0 at h
    simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at h
    omega
  obtain ⟨k, _, hkS, hkF, hkP⟩ :=
    generatedFeasibleContainingE7_frame_root_normalize (leechIntegralAction e P) heN heP he2
  refine ⟨k * e, ?_, ?_, ?_⟩
  · rw [generatedFeasibleContaining_selected_source_word]
    apply generatedAxisE8_preserving_image
    intro v
    rw [map_mul, LinearEquiv.mul_apply, generatedOctadSupported_standard,
      hkS, ← generatedOctadSupported_standard]
    exact heS v
  · rw [map_mul, LinearEquiv.mul_apply]
    exact hkP
  · rw [map_mul, LinearEquiv.mul_apply, heU, hkF]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingOctadStabilizerKernel

/-! Exact actual A orbit size of the source-defined containing-octad feasible destination. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The actual first-axis stabilizer of the containing-octad feasible destination. -/
def generatedFeasibleContainingDestinationStabilizer :
    Subgroup (localAxisStabilizer generatedFeasiblePhysicalRootPair) :=
  MulAction.stabilizer (localAxisStabilizer generatedFeasiblePhysicalRootPair)
    generatedFeasibleContainingOctadDestination

/-- The original local representation transports whole-vector fixation by conjugation. -/
theorem generatedFeasibleContaining_conjugate_fixes (h k : H) (x y : GriessSpace)
    (hh : rhoLocal h x = y) (hk : rhoLocal k x = x) :
    rhoLocal (h * k * h⁻¹) y = y := by
  have hi : rhoLocal h⁻¹ y = x := by
    rw [← hh, map_inv]
    exact (rhoLocal h).symm_apply_apply x
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hi, hk, hh]

/-- The inverse original local word reverses its proved full-vector transport. -/
theorem generatedFeasibleContaining_inverse_transports (h : H) (x y : GriessSpace)
    (hh : rhoLocal h x = y) : rhoLocal h⁻¹ y = x := by
  rw [← hh, map_inv]
  exact (rhoLocal h).symm_apply_apply x

/-- Any genuine simultaneous source transport conjugates the entire actual two-axis stabilizers. -/
def generatedFeasibleContainingStabilizerEquiv (h : H)
    (hfirst : rhoLocal h
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasibleContainingIncidentPair)) 0)
    (hdest : rhoLocal h generatedFeasibleContainingOctadDestination =
      generatedOctadLocalAxis 0 0) :
    generatedFeasibleContainingDestinationStabilizer ≃*
      generatedFeasibleContainingIncidentStabilizer where
  toFun g := by
    have hgfirst : rhoLocal g.val.val
        (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
      conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 := by
      rw [conwayShortAxis_pair_zero]
      exact g.val.property
    refine ⟨⟨h * g.val.val * h⁻¹, ?_⟩, ?_⟩
    · change rhoLocal (h * g.val.val * h⁻¹)
        (conwayAxis generatedFeasibleContainingIncidentPair) =
          conwayAxis generatedFeasibleContainingIncidentPair
      simpa only [conwayShortAxis_pair_zero] using
        generatedFeasibleContaining_conjugate_fixes h g.val.val _ _ hfirst hgfirst
    · change rhoLocal (h * g.val.val * h⁻¹) (generatedOctadLocalAxis 0 0) =
        generatedOctadLocalAxis 0 0
      exact generatedFeasibleContaining_conjugate_fixes h g.val.val _ _ hdest g.property
  invFun g := by
    have hgfirst : rhoLocal g.val.val
        (conwayShortAxis (Sum.inl (0, generatedFeasibleContainingIncidentPair)) 0) =
      conwayShortAxis (Sum.inl (0, generatedFeasibleContainingIncidentPair)) 0 := by
      rw [conwayShortAxis_pair_zero]
      exact g.val.property
    refine ⟨⟨h⁻¹ * g.val.val * h, ?_⟩, ?_⟩
    · have hi := generatedFeasibleContaining_inverse_transports h _ _ hfirst
      change rhoLocal (h⁻¹ * g.val.val * h) (conwayAxis generatedFeasiblePhysicalRootPair) =
        conwayAxis generatedFeasiblePhysicalRootPair
      simpa only [inv_inv, conwayShortAxis_pair_zero] using
        generatedFeasibleContaining_conjugate_fixes h⁻¹ g.val.val _ _ hi hgfirst
    · have hi := generatedFeasibleContaining_inverse_transports h _ _ hdest
      change rhoLocal (h⁻¹ * g.val.val * h) generatedFeasibleContainingOctadDestination =
        generatedFeasibleContainingOctadDestination
      simpa only [inv_inv] using
        generatedFeasibleContaining_conjugate_fixes h⁻¹ g.val.val _ _ hi g.property
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    change h⁻¹ * (h * g.val.val * h⁻¹) * h = g.val.val
    group
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    change h * (h⁻¹ * g.val.val * h) * h⁻¹ = g.val.val
    group
  map_mul' g k := by
    apply Subtype.ext
    apply Subtype.ext
    change h * (g.val.val * k.val.val) * h⁻¹ =
      (h * g.val.val * h⁻¹) * (h * k.val.val * h⁻¹)
    group

/-- The entire source containing-destination A stabilizer has the proved exact incident order. -/
theorem generatedFeasibleContainingDestinationStabilizer_card :
    Nat.card generatedFeasibleContainingDestinationStabilizer = 97409858273280 := by
  obtain ⟨h, hfirst, hdest⟩ := generatedFeasibleContaining_source_transport
  rw [Nat.card_congr (generatedFeasibleContainingStabilizerEquiv h hfirst hdest).toEquiv]
  exact generatedFeasibleContainingIncidentStabilizer_card

/-- The source containing-destination stabilizer has actual index 7,286,400 in A. -/
theorem generatedFeasibleContainingDestinationStabilizer_index :
    generatedFeasibleContainingDestinationStabilizer.index = 7286400 := by
  have h := generatedFeasibleContainingDestinationStabilizer.card_mul_index
  rw [generatedFeasibleContainingDestinationStabilizer_card,
    localAxisStabilizer_card_of_co1_card _ co1_card_exact] at h
  omega

/-- Exactly 7,286,400 original vectors form the containing-octad feasible A orbit. -/
theorem generatedFeasibleContainingOctad_actual_A_orbit_card :
    Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination) = 7286400 := by
  have h := generatedFeasibleContainingDestinationStabilizer_index
  rw [generatedFeasibleContainingDestinationStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq] at h
  exact h

/-- Exactly 63 genuine transitions from the containing-octad A orbit return to secondary. -/
theorem generatedFeasibleActualTransition_containing_secondary_card :
    Nat.card (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)) = 63 := by
  have h := generatedFeasibleActualTransition_containing_secondary_equation
  rw [generatedFeasibleContainingOctad_actual_A_orbit_card] at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

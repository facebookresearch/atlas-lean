/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOddDestinationStabilizerKernel
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingOctadOrbitCount

/-! Exact actual A orbit size of the source-defined odd feasible destination. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The actual first-axis stabilizer of the odd feasible destination. -/
def generatedFeasibleOddSourceDestinationStabilizer :
    Subgroup (localAxisStabilizer generatedFeasiblePhysicalRootPair) :=
  MulAction.stabilizer (localAxisStabilizer generatedFeasiblePhysicalRootPair)
    generatedFeasibleSecondaryOddDestination

/-- Any genuine simultaneous source transport conjugates the entire actual two-axis stabilizers. -/
def generatedFeasibleOddSourceStabilizerEquiv (h : H)
    (hfirst : rhoLocal h
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasibleOddDestinationPair)) 0)
    (hdest : rhoLocal h generatedFeasibleSecondaryOddDestination =
      generatedOddAxis) :
    generatedFeasibleOddSourceDestinationStabilizer ≃*
      generatedFeasibleOddDestinationStabilizer where
  toFun g := by
    have hgfirst : rhoLocal g.val.val
        (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
      conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 := by
      rw [conwayShortAxis_pair_zero]
      exact g.val.property
    refine ⟨⟨h * g.val.val * h⁻¹, ?_⟩, ?_⟩
    · change rhoLocal (h * g.val.val * h⁻¹)
        (conwayAxis generatedFeasibleOddDestinationPair) =
          conwayAxis generatedFeasibleOddDestinationPair
      simpa only [conwayShortAxis_pair_zero] using
        generatedFeasibleContaining_conjugate_fixes h g.val.val _ _ hfirst hgfirst
    · change rhoLocal (h * g.val.val * h⁻¹) (generatedOddAxis) =
        generatedOddAxis
      exact generatedFeasibleContaining_conjugate_fixes h g.val.val _ _ hdest g.property
  invFun g := by
    have hgfirst : rhoLocal g.val.val
        (conwayShortAxis (Sum.inl (0, generatedFeasibleOddDestinationPair)) 0) =
      conwayShortAxis (Sum.inl (0, generatedFeasibleOddDestinationPair)) 0 := by
      rw [conwayShortAxis_pair_zero]
      exact g.val.property
    refine ⟨⟨h⁻¹ * g.val.val * h, ?_⟩, ?_⟩
    · have hi := generatedFeasibleContaining_inverse_transports h _ _ hfirst
      change rhoLocal (h⁻¹ * g.val.val * h) (conwayAxis generatedFeasiblePhysicalRootPair) =
        conwayAxis generatedFeasiblePhysicalRootPair
      simpa only [inv_inv, conwayShortAxis_pair_zero] using
        generatedFeasibleContaining_conjugate_fixes h⁻¹ g.val.val _ _ hi hgfirst
    · have hi := generatedFeasibleContaining_inverse_transports h _ _ hdest
      change rhoLocal (h⁻¹ * g.val.val * h) generatedFeasibleSecondaryOddDestination =
        generatedFeasibleSecondaryOddDestination
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

/-- The entire source odd-destination A stabilizer has the proved exact orthogonal order. -/
theorem generatedFeasibleOddSourceDestinationStabilizer_card :
    Nat.card generatedFeasibleOddSourceDestinationStabilizer = 169114337280 := by
  obtain ⟨h, hfirst, hdest⟩ := generatedFeasibleOddDestination_source_transport
  rw [Nat.card_congr (generatedFeasibleOddSourceStabilizerEquiv h hfirst hdest).toEquiv]
  exact generatedFeasibleOddDestinationStabilizer_card

/-- The source odd-destination stabilizer has actual index 4,196,966,400 in A. -/
theorem generatedFeasibleOddSourceDestinationStabilizer_index :
    generatedFeasibleOddSourceDestinationStabilizer.index = 4196966400 := by
  have h := generatedFeasibleOddSourceDestinationStabilizer.card_mul_index
  rw [generatedFeasibleOddSourceDestinationStabilizer_card,
    localAxisStabilizer_card_of_co1_card _ co1_card_exact] at h
  omega

/-- Exactly 4,196,966,400 original vectors form the odd feasible A orbit. -/
theorem generatedFeasibleOddDestination_actual_A_orbit_card :
    Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleSecondaryOddDestination) = 4196966400 := by
  have h := generatedFeasibleOddSourceDestinationStabilizer_index
  rw [generatedFeasibleOddSourceDestinationStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq] at h
  exact h

/-- Exactly one genuine transition from the odd A orbit returns to secondary. -/
theorem generatedFeasibleActualTransition_odd_secondary_card :
    Nat.card (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      generatedFeasibleSecondaryOddDestination
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)) = 1 := by
  have h := generatedFeasibleActualTransition_odd_secondary_equation
  rw [generatedFeasibleOddDestination_actual_A_orbit_card] at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

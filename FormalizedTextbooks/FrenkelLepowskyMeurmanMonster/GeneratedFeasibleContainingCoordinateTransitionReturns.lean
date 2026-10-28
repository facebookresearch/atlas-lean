/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingCoordinateNOrbits

/-! Actual triality returns of the two containing coordinate phase orbits. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Every simultaneous image of an actual A-orbit vector is still in that same actual A orbit. -/
theorem generatedFeasibleContaining_NOrbit_subset_A (x a : GriessSpace)
    (hx : x ∈ MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair) a) :
    generatedFeasibleContainingCoordinateNOrbit x ⊆
      MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair) a := by
  rintro y ⟨n, hn⟩
  change rhoLocal n.val x = y at hn
  obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hx
  refine MulAction.mem_orbit_iff.mpr ⟨⟨n.val, n.property.1⟩ * h, ?_⟩
  change rhoLocal (n.val * h.val) a = y
  rw [map_mul, LinearEquiv.mul_apply]
  change rhoLocal h.val a = x at hh
  rwa [hh]

/-- Actual triality takes the first containing coordinate orbit onto the second. -/
theorem generatedFeasibleContainingCoordinateFirst_triality :
    sExtra '' generatedFeasibleContainingCoordinateNOrbit
      generatedFeasibleContainingOctadDestination =
        generatedFeasibleContainingCoordinateNOrbit generatedFeasibleContainingTrialitySquare :=
  generatedFeasibleContaining_N_triality_image _

/-- Actual triality takes the second containing coordinate orbit onto the original
containing-pair secondary short sector. -/
theorem generatedFeasibleContainingCoordinateSecond_triality :
    sExtra '' generatedFeasibleContainingCoordinateNOrbit
      generatedFeasibleContainingTrialitySquare = generatedFeasibleContainingOctadAxes := by
  rw [generatedFeasibleContaining_N_triality_image, generatedFeasibleContainingTrialitySquare,
    generatedFeasibleContainingOctadDestination, sExtra_triple]
  exact generatedFeasibleContainingOctadOrbit_eq_axes

/-- Every first coordinate-sector vector gives a genuine containing-class self return. -/
theorem generatedFeasibleContainingCoordinateFirst_self_return :
    generatedFeasibleContainingCoordinateNOrbit generatedFeasibleContainingOctadDestination ⊆
      generatedFeasibleTransitionVectors generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination
          generatedFeasibleContainingOctadDestination := by
  intro x hx
  constructor
  · exact generatedFeasibleContaining_NOrbit_subset_A _ _
      (MulAction.mem_orbit_self _) hx
  · apply generatedFeasibleContaining_NOrbit_subset_A _ _
      generatedFeasibleContainingTrialitySquare_mem
    rw [← generatedFeasibleContainingCoordinateFirst_triality]
    exact ⟨x, hx, rfl⟩

/-- Every second coordinate-sector vector gives a genuine return to the secondary class. -/
theorem generatedFeasibleContainingCoordinateSecond_secondary_return :
    generatedFeasibleContainingCoordinateNOrbit generatedFeasibleContainingTrialitySquare ⊆
      generatedFeasibleTransitionVectors generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination
          (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) := by
  intro x hx
  constructor
  · exact generatedFeasibleContaining_NOrbit_subset_A _ _
      generatedFeasibleContainingTrialitySquare_mem hx
  · have hi : sExtra x ∈ generatedFeasibleContainingOctadAxes := by
      rw [← generatedFeasibleContainingCoordinateSecond_triality]
      exact ⟨x, hx, rfl⟩
    rw [← generatedFeasibleContainingOctadOrbit_eq_axes] at hi
    obtain ⟨n, hn⟩ := hi
    change rhoLocal n.val (conwayShortAxis generatedFeasibleContainingOctadPrototypeLabel 0) =
      sExtra x at hn
    have hp := generatedFeasibleSecondaryNonPair_axis_mem 0
      generatedFeasibleContainingOctadPrototypeLabel
        generatedFeasibleContainingOctadPrototypeLabel_mem 0
    exact generatedFeasibleContaining_NOrbit_subset_A _ _ hp ⟨n, hn⟩

/-- The full actual containing-to-secondary vector fiber has 4928 elements. -/
theorem generatedFeasibleContainingCoordinate_secondary_return_card :
    Nat.card (generatedFeasibleTransitionVectors generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination
        (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)) = 4928 := by
  rw [generatedFeasibleTransition_vectors_card_reverse]
  exact generatedFeasibleActualTransition_secondary_containing_vectors_card

/-- The second coordinate orbit is the entire genuine containing-to-secondary vector fiber. -/
theorem generatedFeasibleContainingCoordinate_secondary_return_eq :
    generatedFeasibleContainingCoordinateNOrbit generatedFeasibleContainingTrialitySquare =
      generatedFeasibleTransitionVectors generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination
          (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) := by
  have : Finite (generatedFeasibleTransitionVectors generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination
        (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)) :=
    Nat.finite_of_card_ne_zero (by
      rw [generatedFeasibleContainingCoordinate_secondary_return_card]
      decide)
  apply Set.eq_of_subset_of_ncard_le
    generatedFeasibleContainingCoordinateSecond_secondary_return
  · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
      generatedFeasibleContainingCoordinate_secondary_return_card,
      generatedFeasibleContainingCoordinateSecondNOrbit_card]

/-- The original two disjoint containing coordinate phase sectors. -/
def generatedFeasibleContainingCoordinatePhaseSectors : Set GriessSpace :=
  generatedFeasibleContainingCoordinateNOrbit generatedFeasibleContainingOctadDestination ∪
    generatedFeasibleContainingCoordinateNOrbit generatedFeasibleContainingTrialitySquare

/-- The two genuine coordinate sectors together contain exactly 9856 actual axes. -/
theorem generatedFeasibleContainingCoordinatePhaseSectors_card :
    Nat.card generatedFeasibleContainingCoordinatePhaseSectors = 9856 := by
  have : Finite (generatedFeasibleContainingCoordinateNOrbit
      generatedFeasibleContainingOctadDestination) :=
    Nat.finite_of_card_ne_zero (by
      rw [generatedFeasibleContainingCoordinateFirstNOrbit_card]
      decide)
  have : Finite (generatedFeasibleContainingCoordinateNOrbit
      generatedFeasibleContainingTrialitySquare) :=
    Nat.finite_of_card_ne_zero (by
      rw [generatedFeasibleContainingCoordinateSecondNOrbit_card]
      decide)
  rw [generatedFeasibleContainingCoordinatePhaseSectors, Nat.card_coe_set_eq,
    Set.ncard_union_eq generatedFeasibleContainingCoordinateNOrbits_disjoint,
    ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    generatedFeasibleContainingCoordinateFirstNOrbit_card,
    generatedFeasibleContainingCoordinateSecondNOrbit_card]

/-- Both actual coordinate sectors lie in the original containing A orbit. -/
theorem generatedFeasibleContainingCoordinatePhaseSectors_subset_A :
    generatedFeasibleContainingCoordinatePhaseSectors ⊆
      MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
        generatedFeasibleContainingOctadDestination := by
  apply Set.union_subset
  · exact generatedFeasibleContaining_NOrbit_subset_A _ _
      (MulAction.mem_orbit_self _)
  · exact generatedFeasibleContaining_NOrbit_subset_A _ _
      generatedFeasibleContainingTrialitySquare_mem

private def uniformSetPreimageEquiv {α β γ : Type*} (f : α → β) (S : Set β)
    (hf : ∀ b, {a // f a = b} ≃ γ) : (f ⁻¹' S) ≃ S × γ := by
  let e : α ≃ β × γ := (Equiv.sigmaFiberEquiv f).symm.trans
    (Equiv.sigmaEquivProdOfEquiv hf)
  exact (Equiv.subtypeEquiv e (fun _ => Iff.rfl)).trans
    Equiv.prodSubtypeFstEquivSubtypeProd

private theorem uniformSetPreimageCard {α β γ : Type*} (f : α → β) (S : Set β)
    (hf : ∀ b, {a // f a = b} ≃ γ) :
    Nat.card (f ⁻¹' S) = Nat.card S * Nat.card γ := by
  rw [Nat.card_congr (uniformSetPreimageEquiv f S hf), Nat.card_prod]

/-- Genuine transition cosets whose original containing-axis image lies in a specified
simultaneous coordinate sector. -/
def generatedFeasibleContainingCoordinateSectorCosets (y : GriessSpace) :
    Set (generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair) :=
  {c | ∃ h : localAxisStabilizer generatedFeasiblePhysicalRootPair,
    Quotient.mk (QuotientGroup.rightRel
      (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h = c ∧
        rhoLocal h.val generatedFeasibleContainingOctadDestination ∈
          generatedFeasibleContainingCoordinateNOrbit y}

private theorem sector_preimage (y : GriessSpace) :
    (fun h : localAxisStabilizer generatedFeasiblePhysicalRootPair =>
      Quotient.mk (QuotientGroup.rightRel
        (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h) ⁻¹'
          generatedFeasibleContainingCoordinateSectorCosets y =
      {h : localAxisStabilizer generatedFeasiblePhysicalRootPair |
        rhoLocal h.val generatedFeasibleContainingOctadDestination ∈
          generatedFeasibleContainingCoordinateNOrbit y} := by
  ext h
  constructor
  · rintro ⟨u, hu, n, hn⟩
    have hm := QuotientGroup.rightRel_apply.mp (Quotient.exact' hu)
    change (h * u⁻¹).val ∈ localOmegaStabilizer at hm
    let k : GeneratedFeasibleContainingN :=
      ⟨(h * u⁻¹).val * n.val,
        (localAxisStabilizer generatedFeasiblePhysicalRootPair).mul_mem
          (h * u⁻¹).property n.property.1,
        localOmegaStabilizer.mul_mem hm n.property.2⟩
    refine ⟨k, ?_⟩
    change rhoLocal ((h.val * u.val⁻¹) * n.val) y =
      rhoLocal h.val generatedFeasibleContainingOctadDestination
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    change rhoLocal n.val y = rhoLocal u.val generatedFeasibleContainingOctadDestination at hn
    rw [hn, map_inv]
    change rhoLocal h.val ((rhoLocal u.val).symm
      (rhoLocal u.val generatedFeasibleContainingOctadDestination)) = _
    rw [LinearEquiv.symm_apply_apply]
  · intro hh
    exact ⟨h, rfl, hh⟩

private def sectorOrbitEquiv (y : GriessSpace)
    (hy : generatedFeasibleContainingCoordinateNOrbit y ⊆
      MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
        generatedFeasibleContainingOctadDestination) :
    {x : MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination //
        x.val ∈ generatedFeasibleContainingCoordinateNOrbit y} ≃
      generatedFeasibleContainingCoordinateNOrbit y where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, hy x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Each genuine coordinate-sector quotient satisfies the actual vector/stabilizer balance. -/
theorem generatedFeasibleContainingCoordinateSector_balance (y : GriessSpace)
    (hy : generatedFeasibleContainingCoordinateNOrbit y ⊆
      MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
        generatedFeasibleContainingOctadDestination) :
    Nat.card (generatedFeasibleContainingCoordinateSectorCosets y) *
      Nat.card (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair) =
        Nat.card (generatedFeasibleContainingCoordinateNOrbit y) *
          Nat.card generatedFeasibleContainingDestinationStabilizer := by
  have hc := uniformSetPreimageCard
    (fun h : localAxisStabilizer generatedFeasiblePhysicalRootPair =>
      Quotient.mk (QuotientGroup.rightRel
        (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h)
    (generatedFeasibleContainingCoordinateSectorCosets y)
    (generatedFeasibleTransitionCosetFiberEquiv generatedFeasiblePhysicalRootPair)
  have ho := uniformSetPreimageCard
    (generatedFeasibleActualOrbitMap generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination)
    {x : MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination |
        x.val ∈ generatedFeasibleContainingCoordinateNOrbit y}
    (generatedFeasibleActualOrbitFiberEquiv generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination)
  have hs : Nat.card ({x : MulAction.orbit
      (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination |
        x.val ∈ generatedFeasibleContainingCoordinateNOrbit y} : Set _) =
      Nat.card (generatedFeasibleContainingCoordinateNOrbit y) :=
    Nat.card_congr (sectorOrbitEquiv y hy)
  rw [hs] at ho
  rw [sector_preimage] at hc
  exact hc.symm.trans ho

/-- The first actual coordinate sector contributes precisely 63 genuine transition cosets. -/
theorem generatedFeasibleContainingCoordinateFirst_cosets_card :
    Nat.card (generatedFeasibleContainingCoordinateSectorCosets
      generatedFeasibleContainingOctadDestination) = 63 := by
  have h := generatedFeasibleContainingCoordinateSector_balance
    generatedFeasibleContainingOctadDestination
    (generatedFeasibleContaining_NOrbit_subset_A _ _ (MulAction.mem_orbit_self _))
  rw [generatedFeasibleContainingCoordinateFirstNOrbit_card,
    generatedFeasibleContainingDestinationStabilizer_card,
    Nat.card_congr (localFeasibleTransitionEquiv generatedFeasiblePhysicalRootPair).toEquiv,
    localOmegaAxisIntersection_card] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 7619615580487680) h

/-- The second actual coordinate sector contributes precisely 63 genuine transition cosets. -/
theorem generatedFeasibleContainingCoordinateSecond_cosets_card :
    Nat.card (generatedFeasibleContainingCoordinateSectorCosets
      generatedFeasibleContainingTrialitySquare) = 63 := by
  have h := generatedFeasibleContainingCoordinateSector_balance
    generatedFeasibleContainingTrialitySquare
    (generatedFeasibleContaining_NOrbit_subset_A _ _ generatedFeasibleContainingTrialitySquare_mem)
  rw [generatedFeasibleContainingCoordinateSecondNOrbit_card,
    generatedFeasibleContainingDestinationStabilizer_card,
    Nat.card_congr (localFeasibleTransitionEquiv generatedFeasiblePhysicalRootPair).toEquiv,
    localOmegaAxisIntersection_card] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 7619615580487680) h

/-- Original sector cosets give actual destination cosets whenever all sector vectors
have that proved actual triality destination. -/
theorem generatedFeasibleContainingCoordinateSectorCosets_subset (y b : GriessSpace)
    (hy : generatedFeasibleContainingCoordinateNOrbit y ⊆
      generatedFeasibleTransitionVectors generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination b) :
    generatedFeasibleContainingCoordinateSectorCosets y ⊆
      generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination b := by
  rintro c ⟨h, rfl, hh⟩
  change Quotient.mk (MulAction.orbitRel
    (localAxisStabilizer generatedFeasiblePhysicalRootPair) GriessSpace)
      (sExtra (rhoLocal h.val generatedFeasibleContainingOctadDestination)) =
        Quotient.mk (MulAction.orbitRel
          (localAxisStabilizer generatedFeasiblePhysicalRootPair) GriessSpace) b
  exact Quotient.sound' (MulAction.orbitRel_apply.mpr (hy hh).2)

/-- The second coordinate-sector cosets are precisely the entire actual secondary-return fiber. -/
theorem generatedFeasibleContainingCoordinateSecond_cosets_eq :
    generatedFeasibleContainingCoordinateSectorCosets generatedFeasibleContainingTrialitySquare =
      generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination
          (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) := by
  apply Set.Subset.antisymm
  · exact generatedFeasibleContainingCoordinateSectorCosets_subset _ _
      generatedFeasibleContainingCoordinateSecond_secondary_return
  · intro c
    induction c using Quotient.inductionOn with
    | h h =>
      intro hc
      refine ⟨h, rfl, ?_⟩
      rw [generatedFeasibleContainingCoordinate_secondary_return_eq]
      refine ⟨MulAction.mem_orbit _ h, ?_⟩
      change Quotient.mk (MulAction.orbitRel
        (localAxisStabilizer generatedFeasiblePhysicalRootPair) GriessSpace)
          (sExtra (rhoLocal h.val generatedFeasibleContainingOctadDestination)) =
            Quotient.mk (MulAction.orbitRel
              (localAxisStabilizer generatedFeasiblePhysicalRootPair) GriessSpace)
                (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) at hc
      exact MulAction.orbitRel_apply.mp (Quotient.exact' hc)

/-- The actual containing self-return column has at least the 63 proved coordinate-sector cosets.
No assertion about the remaining noncoordinate sections is used. -/
theorem generatedFeasibleContainingCoordinate_self_return_lower :
    63 ≤ Nat.card (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination generatedFeasibleContainingOctadDestination) := by
  have : Finite (generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair) :=
    Nat.finite_of_card_ne_zero (by
      rw [generatedFeasibleTransitionCosetSpace_card]
      decide)
  have h := Set.ncard_le_ncard
    (generatedFeasibleContainingCoordinateSectorCosets_subset _ _
      generatedFeasibleContainingCoordinateFirst_self_return)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    generatedFeasibleContainingCoordinateFirst_cosets_card] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

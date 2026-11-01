/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSeventhSlotFeasibility
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSeventhSlotTriangleAttainment
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSixthSlotDistinct

/-! The actual feasible A orbit for source slot 8 (label 6C1) of Höhn–Seysen,
arXiv:2508.01037, Table 3. The counted seventh prototype is transported by a genuine local
element carrying its first triangle root axis to the physical first axis. The entire actual A
stabilizer of the prototype is identified, by genuine conjugation, with the stabilizer of the
first triangle root axis inside the closed seventh H stabilizer. That root axis has the proved
three-element orbit, so the A stabilizer has 106,168,320 elements and the A orbit has
6,685,301,145,600 vectors. The orbit is distinct from the seven closed feasible A orbits. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A genuine local element carries the first positive triangle root axis to the first axis. -/
theorem generatedFeasibleSeventhSlot_transport_exists : ∃ k : H,
    rhoLocal k (conwayShortAxis (Sum.inl (0, generatedSeventhTargetPair 0)) 0) =
      conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 :=
  generatedAxis_local_signed_transitive _ _ 0 0

/-- A chosen genuine local transport of the first triangle root axis to the first axis. -/
def generatedFeasibleSeventhSlotTransport : H :=
  Classical.choose generatedFeasibleSeventhSlot_transport_exists

/-- The chosen transport carries the positive triangle root axis to the first axis. -/
theorem generatedFeasibleSeventhSlotTransport_first :
    rhoLocal generatedFeasibleSeventhSlotTransport
      (conwayShortAxis (Sum.inl (0, generatedSeventhTargetPair 0)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 :=
  Classical.choose_spec generatedFeasibleSeventhSlot_transport_exists

/-- The chosen transport carries the opposite triangle root axis to the opposite first axis. -/
theorem generatedFeasibleSeventhSlotTransport_opposite :
    rhoLocal generatedFeasibleSeventhSlotTransport
      (conwayShortAxis (Sum.inl (0, generatedSeventhTargetPair 0)) 1) =
        conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1 :=
  generatedFeasibleSixthSlot_local_opposite _ _ _ generatedFeasibleSeventhSlotTransport_first

/-- The slot-8 feasible prototype: the genuine local image of the counted seventh prototype. -/
def generatedFeasibleSeventhSlotPrototype : GriessSpace :=
  rhoLocal generatedFeasibleSeventhSlotTransport generatedSeventhAxis

/-- The prototype lies in the actual H orbit of the counted seventh prototype. -/
theorem generatedFeasibleSeventhSlotPrototype_mem_seventh_orbit :
    generatedFeasibleSeventhSlotPrototype ∈ MulAction.orbit H generatedSeventhAxis :=
  ⟨generatedFeasibleSeventhSlotTransport, rfl⟩

/-- The prototype lies in the actual full feasible orbit: the orbit of the opposite axis
under the entire generated stabilizer of the first axis. -/
theorem generatedFeasibleSeventhSlotPrototype_feasible :
    generatedFeasibleSeventhSlotPrototype ∈ generatedFeasibleVectorOrbit
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0)
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1) := by
  have h := generatedFeasibleSixthSlot_orbit_local generatedFeasibleSeventhSlotTransport
    (generatedFeasibleSeventhSlot_prototype_feasible_root 0)
  rwa [generatedFeasibleSeventhSlotTransport_first,
    generatedFeasibleSeventhSlotTransport_opposite] at h

/-- The entire actual A orbit of the prototype consists of genuinely feasible axes. -/
theorem generatedFeasibleSeventhSlot_A_orbit_subset :
    MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
        generatedFeasibleSeventhSlotPrototype ⊆
      generatedFeasibleVectorOrbit
        (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0)
        (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1) := by
  rintro x ⟨g, rfl⟩
  refine generatedFeasibleSixthSlot_orbit_fixed (localIntoGenerated g.val) ?_
    generatedFeasibleSeventhSlotPrototype_feasible
  exact localAxisStabilizer_signedAxis_fixed g.val _ g.property 0

/-- The transported first triangle root axis is the first axis itself. -/
theorem generatedFeasibleSeventhSlotTransport_root :
    rhoLocal generatedFeasibleSeventhSlotTransport (generatedFeasibleSeventhSlotRootAxis 0) =
      conwayAxis generatedFeasiblePhysicalRootPair := by
  rw [← conwayShortAxis_pair_zero]
  exact generatedFeasibleSeventhSlotTransport_first

/-- Every genuine local transport of any positive triangle root axis to the first axis carries
the counted seventh prototype into the actual A orbit of the chosen prototype. -/
theorem generatedFeasibleSeventhSlot_transport_mem_orbit (j : Fin 3) (k : H)
    (hk : rhoLocal k (generatedFeasibleSeventhSlotRootAxis j) =
      conwayAxis generatedFeasiblePhysicalRootPair) :
    rhoLocal k generatedSeventhAxis ∈
      MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
        generatedFeasibleSeventhSlotPrototype := by
  have hj : generatedFeasibleSeventhSlotRootAxis j ∈ MulAction.orbit
      generatedSeventhLocalAxisStabilizer (generatedFeasibleSeventhSlotRootAxis 0) := by
    rw [generatedFeasibleSeventhSlot_root_orbit_eq]
    exact ⟨j, rfl⟩
  obtain ⟨s, hs⟩ := hj
  have hs' : rhoLocal s.val (generatedFeasibleSeventhSlotRootAxis 0) =
      generatedFeasibleSeventhSlotRootAxis j := hs
  have hfix : rhoLocal s.val generatedSeventhAxis = generatedSeventhAxis := s.property
  have hA : k * s.val * generatedFeasibleSeventhSlotTransport⁻¹ ∈
      localAxisStabilizer generatedFeasiblePhysicalRootPair := by
    change rhoLocal (k * s.val * generatedFeasibleSeventhSlotTransport⁻¹)
      (conwayAxis generatedFeasiblePhysicalRootPair) = conwayAxis generatedFeasiblePhysicalRootPair
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      generatedFeasibleSixthSlot_local_inverse _ generatedFeasibleSeventhSlotTransport_root, hs',
      hk]
  refine ⟨⟨k * s.val * generatedFeasibleSeventhSlotTransport⁻¹, hA⟩, ?_⟩
  change rhoLocal (k * s.val * generatedFeasibleSeventhSlotTransport⁻¹)
    (rhoLocal generatedFeasibleSeventhSlotTransport generatedSeventhAxis) = _
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    generatedFeasibleSixthSlot_local_inverse _ (x := generatedSeventhAxis) rfl, hfix]

/-- The actual A stabilizer of the prototype. -/
def generatedFeasibleSeventhSlotStabilizer :
    Subgroup (localAxisStabilizer generatedFeasiblePhysicalRootPair) :=
  MulAction.stabilizer (localAxisStabilizer generatedFeasiblePhysicalRootPair)
    generatedFeasibleSeventhSlotPrototype

/-- The stabilizer of the first triangle root axis inside the actual seventh H stabilizer. -/
def generatedFeasibleSeventhSlotRootStabilizer : Subgroup generatedSeventhLocalAxisStabilizer :=
  MulAction.stabilizer generatedSeventhLocalAxisStabilizer (generatedFeasibleSeventhSlotRootAxis 0)

/-- The entire actual A stabilizer of the prototype is conjugate to the stabilizer of the first
triangle root axis inside the entire seventh H stabilizer. -/
def generatedFeasibleSeventhSlotStabilizerEquiv :
    generatedFeasibleSeventhSlotStabilizer ≃* generatedFeasibleSeventhSlotRootStabilizer where
  toFun g := by
    have hg : rhoLocal g.val.val generatedFeasibleSeventhSlotPrototype =
        generatedFeasibleSeventhSlotPrototype := g.property
    have ha : rhoLocal g.val.val (conwayAxis generatedFeasiblePhysicalRootPair) =
        conwayAxis generatedFeasiblePhysicalRootPair := g.val.property
    refine ⟨⟨generatedFeasibleSeventhSlotTransport⁻¹ * g.val.val *
      generatedFeasibleSeventhSlotTransport, ?_⟩, ?_⟩
    · have hc := generatedFeasibleSixthSlot_conjugate_fixes
        generatedFeasibleSeventhSlotTransport⁻¹ g.val.val _ _
        (generatedFeasibleSixthSlot_local_inverse _ rfl) hg
      rw [inv_inv] at hc
      exact hc
    · have hc := generatedFeasibleSixthSlot_conjugate_fixes
        generatedFeasibleSeventhSlotTransport⁻¹ g.val.val _ _
        (generatedFeasibleSixthSlot_local_inverse _ generatedFeasibleSeventhSlotTransport_root)
        ha
      rw [inv_inv] at hc
      exact hc
  invFun g := by
    have hg : rhoLocal g.val.val generatedSeventhAxis = generatedSeventhAxis := g.val.property
    have ha : rhoLocal g.val.val (generatedFeasibleSeventhSlotRootAxis 0) =
        generatedFeasibleSeventhSlotRootAxis 0 := g.property
    refine ⟨⟨generatedFeasibleSeventhSlotTransport * g.val.val *
      generatedFeasibleSeventhSlotTransport⁻¹, ?_⟩, ?_⟩
    · exact generatedFeasibleSixthSlot_conjugate_fixes _ _ _ _
        generatedFeasibleSeventhSlotTransport_root ha
    · exact generatedFeasibleSixthSlot_conjugate_fixes _ _ _ _ rfl hg
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    change generatedFeasibleSeventhSlotTransport *
      (generatedFeasibleSeventhSlotTransport⁻¹ * g.val.val *
        generatedFeasibleSeventhSlotTransport) * generatedFeasibleSeventhSlotTransport⁻¹ =
          g.val.val
    group
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    change generatedFeasibleSeventhSlotTransport⁻¹ *
      (generatedFeasibleSeventhSlotTransport * g.val.val *
        generatedFeasibleSeventhSlotTransport⁻¹) * generatedFeasibleSeventhSlotTransport =
          g.val.val
    group
  map_mul' g k := by
    apply Subtype.ext
    apply Subtype.ext
    change generatedFeasibleSeventhSlotTransport⁻¹ * (g.val.val * k.val.val) *
        generatedFeasibleSeventhSlotTransport =
      (generatedFeasibleSeventhSlotTransport⁻¹ * g.val.val *
        generatedFeasibleSeventhSlotTransport) *
        (generatedFeasibleSeventhSlotTransport⁻¹ * k.val.val *
          generatedFeasibleSeventhSlotTransport)
    group

/-- Orbit–stabilizer in the closed seventh H stabilizer: the first triangle root axis has a
three-element orbit, so its stabilizer has exactly 106,168,320 elements. -/
theorem generatedFeasibleSeventhSlotRootStabilizer_card :
    Nat.card generatedFeasibleSeventhSlotRootStabilizer = 106168320 := by
  have hi : generatedFeasibleSeventhSlotRootStabilizer.index = 3 := by
    rw [generatedFeasibleSeventhSlotRootStabilizer, MulAction.index_stabilizer,
      ← Nat.card_coe_set_eq]
    exact generatedFeasibleSeventhSlot_root_orbit_card
  have h := generatedFeasibleSeventhSlotRootStabilizer.card_mul_index
  rw [hi, generatedSeventh_local_stabilizer_card] at h
  omega

/-- The entire actual A stabilizer of the prototype has exactly 106,168,320 elements. -/
theorem generatedFeasibleSeventhSlotStabilizer_card :
    Nat.card generatedFeasibleSeventhSlotStabilizer = 106168320 := by
  rw [Nat.card_congr generatedFeasibleSeventhSlotStabilizerEquiv.toEquiv]
  exact generatedFeasibleSeventhSlotRootStabilizer_card

/-- The prototype's actual A stabilizer has index 6,685,301,145,600 in A. -/
theorem generatedFeasibleSeventhSlotStabilizer_index :
    generatedFeasibleSeventhSlotStabilizer.index = 6685301145600 := by
  have h := generatedFeasibleSeventhSlotStabilizer.card_mul_index
  rw [generatedFeasibleSeventhSlotStabilizer_card,
    localAxisStabilizer_card_of_co1_card _ co1_card_exact] at h
  omega

/-- Exactly 6,685,301,145,600 original vectors form the slot-8 feasible A orbit. -/
theorem generatedFeasibleSeventhSlot_actual_A_orbit_card :
    Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleSeventhSlotPrototype) = 6685301145600 := by
  have h := generatedFeasibleSeventhSlotStabilizer_index
  rw [generatedFeasibleSeventhSlotStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq] at h
  exact h

/-- The proposed size-three reduction for the prototype itself: under its entire actual H
stabilizer, the first axis has exactly the transported triangle catalogue as its orbit. -/
theorem generatedFeasibleSeventhSlot_first_axis_orbit_eq :
    {z | ∃ g ∈ MulAction.stabilizer H generatedFeasibleSeventhSlotPrototype,
        rhoLocal g (conwayAxis generatedFeasiblePhysicalRootPair) = z} =
      Set.range (fun k => rhoLocal generatedFeasibleSeventhSlotTransport
        (generatedFeasibleSeventhSlotRootAxis k)) := by
  ext z
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg' : rhoLocal g generatedFeasibleSeventhSlotPrototype =
        generatedFeasibleSeventhSlotPrototype := hg
    have hs := generatedFeasibleSixthSlot_conjugate_fixes
      generatedFeasibleSeventhSlotTransport⁻¹ g _ _
      (generatedFeasibleSixthSlot_local_inverse _ rfl) hg'
    rw [inv_inv] at hs
    obtain ⟨k, hk⟩ := generatedFeasibleSeventhSlot_coverage _ hs 0
    refine ⟨k, ?_⟩
    have hk' : rhoLocal (generatedFeasibleSeventhSlotTransport⁻¹ * g *
        generatedFeasibleSeventhSlotTransport) (generatedFeasibleSeventhSlotRootAxis 0) =
          generatedFeasibleSeventhSlotRootAxis k := hk
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      generatedFeasibleSeventhSlotTransport_root] at hk'
    change rhoLocal generatedFeasibleSeventhSlotTransport
      (generatedFeasibleSeventhSlotRootAxis k) = _
    rw [← hk', ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  · rintro ⟨k, rfl⟩
    have hk : generatedFeasibleSeventhSlotRootAxis k ∈ MulAction.orbit
        generatedSeventhLocalAxisStabilizer (generatedFeasibleSeventhSlotRootAxis 0) := by
      rw [generatedFeasibleSeventhSlot_root_orbit_eq]
      exact ⟨k, rfl⟩
    obtain ⟨s, hs⟩ := hk
    have hs' : rhoLocal s.val (generatedFeasibleSeventhSlotRootAxis 0) =
        generatedFeasibleSeventhSlotRootAxis k := hs
    have hfix : rhoLocal s.val generatedSeventhAxis = generatedSeventhAxis := s.property
    refine ⟨generatedFeasibleSeventhSlotTransport * s.val *
      generatedFeasibleSeventhSlotTransport⁻¹,
      generatedFeasibleSixthSlot_conjugate_fixes _ _ _ _ rfl hfix, ?_⟩
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      generatedFeasibleSixthSlot_local_inverse _ generatedFeasibleSeventhSlotTransport_root, hs']

/-- The first-axis orbit under the prototype's entire actual H stabilizer has three elements. -/
theorem generatedFeasibleSeventhSlot_first_axis_orbit_card :
    Nat.card {z | ∃ g ∈ MulAction.stabilizer H generatedFeasibleSeventhSlotPrototype,
        rhoLocal g (conwayAxis generatedFeasiblePhysicalRootPair) = z} = 3 := by
  rw [generatedFeasibleSeventhSlot_first_axis_orbit_eq, Nat.card_range_of_injective,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  intro k l h
  exact generatedFeasibleSeventhSlotRootAxis_injective
    ((rhoLocal generatedFeasibleSeventhSlotTransport).injective h)

/-- A vector whose actual A orbit has a different size cannot share the prototype's orbit. -/
theorem generatedFeasibleSeventhSlot_not_mem_of_card_ne {z : GriessSpace}
    (hz : Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair) z) ≠
      6685301145600) :
    generatedFeasibleSeventhSlotPrototype ∉
      MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair) z := by
  intro hx
  apply hz
  rw [← MulAction.orbit_eq_iff.mpr hx]
  exact generatedFeasibleSeventhSlot_actual_A_orbit_card

/-- The prototype lies in none of the seven closed feasible A orbits, listed in Table 3 order:
the opposite axis, the secondary axis, the containing-octad, outside-octad and odd
destinations, the one-eighth destination, and the slot-7 prototype. -/
theorem generatedFeasibleSeventhSlot_not_mem_closed :
    generatedFeasibleSeventhSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1) ∧
      generatedFeasibleSeventhSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) ∧
      generatedFeasibleSeventhSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleContainingOctadDestination ∧
      generatedFeasibleSeventhSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleOutsideOctadDestination ∧
      generatedFeasibleSeventhSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleSecondaryOddDestination ∧
      generatedFeasibleSeventhSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleContainingNewDestination ∧
      generatedFeasibleSeventhSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleSixthSlotPrototype := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply generatedFeasibleSeventhSlot_not_mem_of_card_ne
  · rw [generatedFeasibleActualOrbit_first_card]
    decide
  · change Nat.card (generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair) ≠ _
    rw [generatedFeasibleSecondaryLocalOrbit_card]
    decide
  · rw [generatedFeasibleContainingOctad_actual_A_orbit_card]
    decide
  · rw [generatedFeasibleOutsideOctad_actual_A_orbit_card]
    decide
  · rw [generatedFeasibleOddDestination_actual_A_orbit_card]
    decide
  · rw [generatedFeasibleContainingEighth_actual_A_orbit_card]
    decide
  · rw [generatedFeasibleSixthSlot_actual_A_orbit_card]
    decide

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

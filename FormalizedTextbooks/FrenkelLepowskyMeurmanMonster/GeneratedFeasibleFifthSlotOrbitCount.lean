/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleFifthSlotAttainment
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSixthSlotDistinct

/-! The actual feasible A orbit for source slot 6 (label 4C1) of Höhn–Seysen,
arXiv:2508.01037, Table 3.

The counted fifth prototype is genuinely feasible for the slot axis `4(e₁₂-e₁₃)`, phase 0,
and a genuine local element carries that axis to the physical first axis. The entire actual
A stabilizer of the transported prototype is conjugate to the stabilizer of the slot axis
inside the closed fifth H stabilizer. The slot axis has exactly sixteen images under the
fifth H stabilizer, so orbit–stabilizer gives the A stabilizer order 1,321,205,760 and the
A orbit size 537,211,699,200. No source table value is assumed. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 20000
attribute [local irreducible] generatedFifthAxis

/-- A genuine local element carries the slot axis to the physical first axis. -/
theorem generatedFeasibleFifthSlot_transport_exists : ∃ k : H,
    rhoLocal k generatedFeasibleFifthSlotFirstAxis =
      conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 :=
  generatedAxis_local_signed_transitive _ _ 0 0

/-- A chosen genuine local transport of the slot axis to the first axis. -/
def generatedFeasibleFifthSlotTransport : H :=
  Classical.choose generatedFeasibleFifthSlot_transport_exists

/-- The chosen transport carries the slot axis to the first axis. -/
theorem generatedFeasibleFifthSlotTransport_first :
    rhoLocal generatedFeasibleFifthSlotTransport generatedFeasibleFifthSlotFirstAxis =
      conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 :=
  Classical.choose_spec generatedFeasibleFifthSlot_transport_exists

/-- The chosen transport carries the opposite slot axis to the opposite first axis. -/
theorem generatedFeasibleFifthSlotTransport_opposite :
    rhoLocal generatedFeasibleFifthSlotTransport
      (conwayShortAxis (Sum.inl (0, generatedFeasibleFifthSlotPair)) 1) =
        conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1 :=
  generatedFeasibleSixthSlot_local_opposite _ _ _ generatedFeasibleFifthSlotTransport_first

/-- The slot-6 feasible prototype: the genuine local image of the counted fifth prototype. -/
def generatedFeasibleFifthSlotPrototype : GriessSpace :=
  rhoLocal generatedFeasibleFifthSlotTransport generatedFifthAxis

/-- The prototype lies in the actual H orbit of the counted fifth prototype. -/
theorem generatedFeasibleFifthSlotPrototype_mem_fifth_orbit :
    generatedFeasibleFifthSlotPrototype ∈ MulAction.orbit H generatedFifthAxis :=
  ⟨generatedFeasibleFifthSlotTransport, rfl⟩

/-- The prototype lies in the actual full feasible orbit: the orbit of the opposite axis
under the entire generated stabilizer of the first axis. -/
theorem generatedFeasibleFifthSlotPrototype_feasible :
    generatedFeasibleFifthSlotPrototype ∈ generatedFeasibleVectorOrbit
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0)
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1) := by
  have h := generatedFeasibleSixthSlot_orbit_local generatedFeasibleFifthSlotTransport
    generatedFeasibleFifthSlot_fifth_feasible
  rwa [generatedFeasibleFifthSlotTransport_first,
    generatedFeasibleFifthSlotTransport_opposite] at h

/-- The entire actual A orbit of the prototype consists of genuinely feasible axes. -/
theorem generatedFeasibleFifthSlot_A_orbit_subset :
    MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
        generatedFeasibleFifthSlotPrototype ⊆
      generatedFeasibleVectorOrbit
        (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0)
        (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1) := by
  rintro x ⟨g, rfl⟩
  refine generatedFeasibleSixthSlot_orbit_fixed (localIntoGenerated g.val) ?_
    generatedFeasibleFifthSlotPrototype_feasible
  exact localAxisStabilizer_signedAxis_fixed g.val _ g.property 0

/-- The actual A stabilizer of the prototype. -/
def generatedFeasibleFifthSlotStabilizer :
    Subgroup (localAxisStabilizer generatedFeasiblePhysicalRootPair) :=
  MulAction.stabilizer (localAxisStabilizer generatedFeasiblePhysicalRootPair)
    generatedFeasibleFifthSlotPrototype

/-- The transport in the form used for conjugation: it carries the slot axis to the
physical pair axis. -/
theorem generatedFeasibleFifthSlotTransport_first_axis :
    rhoLocal generatedFeasibleFifthSlotTransport generatedFeasibleFifthSlotFirstAxis =
      conwayAxis generatedFeasiblePhysicalRootPair := by
  rw [generatedFeasibleFifthSlotTransport_first, conwayShortAxis_pair_zero]

/-- The entire actual A stabilizer of the prototype is conjugate to the stabilizer of the slot
axis inside the entire actual fifth H stabilizer. -/
def generatedFeasibleFifthSlotStabilizerEquiv :
    generatedFeasibleFifthSlotStabilizer ≃*
      MulAction.stabilizer generatedFifthLocalAxisStabilizer generatedFeasibleFifthSlotFirstAxis
        where
  toFun g := by
    refine ⟨⟨generatedFeasibleFifthSlotTransport⁻¹ * g.val.val *
      generatedFeasibleFifthSlotTransport, ?_⟩, ?_⟩
    · have hg : rhoLocal g.val.val generatedFeasibleFifthSlotPrototype =
          generatedFeasibleFifthSlotPrototype := g.property
      have hc := generatedFeasibleSixthSlot_conjugate_fixes
        generatedFeasibleFifthSlotTransport⁻¹ g.val.val _ _
        (generatedFeasibleSixthSlot_local_inverse _ rfl) hg
      rw [inv_inv] at hc
      exact hc
    · have hg : rhoLocal g.val.val (conwayAxis generatedFeasiblePhysicalRootPair) =
          conwayAxis generatedFeasiblePhysicalRootPair := g.val.property
      have hc := generatedFeasibleSixthSlot_conjugate_fixes
        generatedFeasibleFifthSlotTransport⁻¹ g.val.val _ _
        (generatedFeasibleSixthSlot_local_inverse _
          generatedFeasibleFifthSlotTransport_first_axis) hg
      rw [inv_inv] at hc
      exact hc
  invFun g := by
    refine ⟨⟨generatedFeasibleFifthSlotTransport * g.val.val *
      generatedFeasibleFifthSlotTransport⁻¹, ?_⟩, ?_⟩
    · have hg : rhoLocal g.val.val generatedFeasibleFifthSlotFirstAxis =
          generatedFeasibleFifthSlotFirstAxis := g.property
      exact generatedFeasibleSixthSlot_conjugate_fixes _ _ _ _
        generatedFeasibleFifthSlotTransport_first_axis hg
    · have hg : rhoLocal g.val.val generatedFifthAxis = generatedFifthAxis := g.val.property
      exact generatedFeasibleSixthSlot_conjugate_fixes _ _ _ _ rfl hg
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    change generatedFeasibleFifthSlotTransport *
      (generatedFeasibleFifthSlotTransport⁻¹ * g.val.val * generatedFeasibleFifthSlotTransport) *
        generatedFeasibleFifthSlotTransport⁻¹ = g.val.val
    group
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    change generatedFeasibleFifthSlotTransport⁻¹ *
      (generatedFeasibleFifthSlotTransport * g.val.val * generatedFeasibleFifthSlotTransport⁻¹) *
        generatedFeasibleFifthSlotTransport = g.val.val
    group
  map_mul' g k := by
    apply Subtype.ext
    apply Subtype.ext
    change generatedFeasibleFifthSlotTransport⁻¹ * (g.val.val * k.val.val) *
        generatedFeasibleFifthSlotTransport =
      (generatedFeasibleFifthSlotTransport⁻¹ * g.val.val * generatedFeasibleFifthSlotTransport) *
        (generatedFeasibleFifthSlotTransport⁻¹ * k.val.val * generatedFeasibleFifthSlotTransport)
    group

/-- Orbit–stabilizer inside the closed fifth H stabilizer: the slot axis has a stabilizer of
order 1,321,205,760 there, because its orbit has exactly sixteen vectors. -/
theorem generatedFeasibleFifthSlot_first_axis_stabilizer_card :
    Nat.card (MulAction.stabilizer generatedFifthLocalAxisStabilizer
      generatedFeasibleFifthSlotFirstAxis) = 1321205760 := by
  have h := (MulAction.stabilizer generatedFifthLocalAxisStabilizer
    generatedFeasibleFifthSlotFirstAxis).card_mul_index
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, generatedFeasibleFifthSlot_orbit_card,
    generatedFifth_local_stabilizer_card] at h
  omega

/-- The entire actual A stabilizer of the prototype has exactly 1,321,205,760 elements. -/
theorem generatedFeasibleFifthSlotStabilizer_card :
    Nat.card generatedFeasibleFifthSlotStabilizer = 1321205760 := by
  rw [Nat.card_congr generatedFeasibleFifthSlotStabilizerEquiv.toEquiv]
  exact generatedFeasibleFifthSlot_first_axis_stabilizer_card

/-- The prototype's actual A stabilizer has index 537,211,699,200 in A. -/
theorem generatedFeasibleFifthSlotStabilizer_index :
    generatedFeasibleFifthSlotStabilizer.index = 537211699200 := by
  have h := generatedFeasibleFifthSlotStabilizer.card_mul_index
  rw [generatedFeasibleFifthSlotStabilizer_card,
    localAxisStabilizer_card_of_co1_card _ co1_card_exact] at h
  omega

/-- Exactly 537,211,699,200 original vectors form the slot-6 feasible A orbit. -/
theorem generatedFeasibleFifthSlot_actual_A_orbit_card :
    Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleFifthSlotPrototype) = 537211699200 := by
  have h := generatedFeasibleFifthSlotStabilizer_index
  rw [generatedFeasibleFifthSlotStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq] at h
  exact h

/-- The actual A stabilizer of the prototype is literally the stabilizer of the first axis
inside the prototype's entire actual H stabilizer. -/
def generatedFeasibleFifthSlotStabilizerFirstEquiv :
    generatedFeasibleFifthSlotStabilizer ≃*
      MulAction.stabilizer (MulAction.stabilizer H generatedFeasibleFifthSlotPrototype)
        (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) where
  toFun g := ⟨⟨g.val.val, g.property⟩,
    localAxisStabilizer_signedAxis_fixed g.val.val _ g.val.property 0⟩
  invFun g := by
    have hg : rhoLocal g.val.val
        (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
          conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 := g.property
    refine ⟨⟨g.val.val, ?_⟩, g.val.property⟩
    change rhoLocal g.val.val (conwayAxis generatedFeasiblePhysicalRootPair) =
      conwayAxis generatedFeasiblePhysicalRootPair
    rw [← conwayShortAxis_pair_zero]
    exact hg
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The entire orbit of the first axis under the prototype's actual H stabilizer is the
genuine transport of the sixteen-element slot catalogue. -/
theorem generatedFeasibleFifthSlot_first_axis_orbit_eq :
    MulAction.orbit (MulAction.stabilizer H generatedFeasibleFifthSlotPrototype)
        (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
      rhoLocal generatedFeasibleFifthSlotTransport ''
        Set.range generatedFeasibleFifthSlotCatalogueAxis := by
  rw [← generatedFeasibleFifthSlot_orbit_eq]
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    have hg : rhoLocal g.val generatedFeasibleFifthSlotPrototype =
        generatedFeasibleFifthSlotPrototype := g.property
    have hv := generatedFeasibleSixthSlot_conjugate_fixes
      generatedFeasibleFifthSlotTransport⁻¹ g.val _ _
      (generatedFeasibleSixthSlot_local_inverse _ rfl) hg
    rw [inv_inv] at hv
    refine ⟨rhoLocal (generatedFeasibleFifthSlotTransport⁻¹ * g.val *
      generatedFeasibleFifthSlotTransport) generatedFeasibleFifthSlotFirstAxis,
      ⟨⟨_, hv⟩, rfl⟩, ?_⟩
    change rhoLocal generatedFeasibleFifthSlotTransport (rhoLocal
      (generatedFeasibleFifthSlotTransport⁻¹ * g.val * generatedFeasibleFifthSlotTransport)
        generatedFeasibleFifthSlotFirstAxis) = rhoLocal g.val
          (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0)
    rw [← LinearEquiv.mul_apply, ← map_mul, map_mul, map_mul, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, generatedFeasibleFifthSlotTransport_first,
      ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel_left]
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    have hg : rhoLocal g.val generatedFifthAxis = generatedFifthAxis := g.property
    refine ⟨⟨generatedFeasibleFifthSlotTransport * g.val *
      generatedFeasibleFifthSlotTransport⁻¹,
      generatedFeasibleSixthSlot_conjugate_fixes _ _ _ _ rfl hg⟩, ?_⟩
    change rhoLocal (generatedFeasibleFifthSlotTransport * g.val *
        generatedFeasibleFifthSlotTransport⁻¹)
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
        rhoLocal generatedFeasibleFifthSlotTransport
          (rhoLocal g.val generatedFeasibleFifthSlotFirstAxis)
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      generatedFeasibleSixthSlot_local_inverse _ generatedFeasibleFifthSlotTransport_first]

/-- The first axis has exactly sixteen images under the prototype's actual H stabilizer. -/
theorem generatedFeasibleFifthSlot_first_axis_orbit_card :
    Nat.card (MulAction.orbit (MulAction.stabilizer H generatedFeasibleFifthSlotPrototype)
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0)) = 16 := by
  rw [generatedFeasibleFifthSlot_first_axis_orbit_eq,
    Nat.card_image_of_injective (rhoLocal generatedFeasibleFifthSlotTransport).injective,
    generatedFeasibleFifthSlotCatalogue_card]

/-- Every genuine local transport of the slot axis to the first axis carries the counted fifth
prototype into the actual A orbit of the chosen prototype. -/
theorem generatedFeasibleFifthSlot_transport_mem_orbit (k : H)
    (hk : rhoLocal k generatedFeasibleFifthSlotFirstAxis =
      conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) :
    rhoLocal k generatedFifthAxis ∈
      MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
        generatedFeasibleFifthSlotPrototype := by
  rw [conwayShortAxis_pair_zero] at hk
  have hA : k * generatedFeasibleFifthSlotTransport⁻¹ ∈
      localAxisStabilizer generatedFeasiblePhysicalRootPair := by
    change rhoLocal (k * generatedFeasibleFifthSlotTransport⁻¹)
      (conwayAxis generatedFeasiblePhysicalRootPair) = conwayAxis generatedFeasiblePhysicalRootPair
    rw [map_mul, LinearEquiv.mul_apply,
      generatedFeasibleSixthSlot_local_inverse _ generatedFeasibleFifthSlotTransport_first_axis, hk]
  refine ⟨⟨k * generatedFeasibleFifthSlotTransport⁻¹, hA⟩, ?_⟩
  change rhoLocal (k * generatedFeasibleFifthSlotTransport⁻¹)
    (rhoLocal generatedFeasibleFifthSlotTransport generatedFifthAxis) = _
  rw [map_mul, LinearEquiv.mul_apply,
    generatedFeasibleSixthSlot_local_inverse _ (x := generatedFifthAxis) rfl]

/-- A vector whose actual A orbit has a different size cannot share the prototype's orbit. -/
theorem generatedFeasibleFifthSlot_not_mem_of_card_ne {z : GriessSpace}
    (hz : Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair) z) ≠
      537211699200) :
    generatedFeasibleFifthSlotPrototype ∉
      MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair) z := by
  intro hx
  apply hz
  rw [← MulAction.orbit_eq_iff.mpr hx]
  exact generatedFeasibleFifthSlot_actual_A_orbit_card

/-- The prototype lies in none of the seven previously closed feasible A orbits, listed in
Table 3 order: the opposite axis, the secondary axis, the containing-octad, outside-octad and
odd destinations, the one-eighth destination and the slot-7 prototype. -/
theorem generatedFeasibleFifthSlot_not_mem_closed :
    generatedFeasibleFifthSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1) ∧
      generatedFeasibleFifthSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) ∧
      generatedFeasibleFifthSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleContainingOctadDestination ∧
      generatedFeasibleFifthSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleOutsideOctadDestination ∧
      generatedFeasibleFifthSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleSecondaryOddDestination ∧
      generatedFeasibleFifthSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleContainingNewDestination ∧
      generatedFeasibleFifthSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleSixthSlotPrototype := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply generatedFeasibleFifthSlot_not_mem_of_card_ne
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

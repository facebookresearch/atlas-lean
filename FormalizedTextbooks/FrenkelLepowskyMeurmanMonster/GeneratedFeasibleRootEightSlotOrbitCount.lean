/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleRootEightSlotRootFixation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSixthSlotOrbitCount
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightActualLocalCount

/-! The actual feasible A orbit for source slot 9 (label 10A1) of Höhn–Seysen,
arXiv:2508.01037, Table 3. The counted root-eight prototype (global family of source Table 1
at zero-based index 9) is transported by a genuine local element carrying its rooted plus pair
axis to the physical first axis. Every actual H fixer of the transported prototype fixes the
first axis, so the entire actual A stabilizer is identified, by genuine conjugation, with the
closed root-eight H stabilizer of order 177,408,000. Hence the A orbit has 4,000,762,036,224
vectors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A genuine local element carries the rooted plus pair axis to the first axis. -/
theorem generatedFeasibleRootEightSlot_transport_exists : ∃ k : H,
    rhoLocal k (conwayShortAxis (Sum.inl (1, 248)) 0) =
      conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 :=
  generatedAxis_local_signed_transitive _ _ 0 0

/-- A chosen genuine local transport of the rooted plus pair axis to the first axis. -/
def generatedFeasibleRootEightSlotTransport : H :=
  Classical.choose generatedFeasibleRootEightSlot_transport_exists

/-- The chosen transport carries the rooted plus pair axis to the first axis. -/
theorem generatedFeasibleRootEightSlotTransport_first :
    rhoLocal generatedFeasibleRootEightSlotTransport (conwayShortAxis (Sum.inl (1, 248)) 0) =
      conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 :=
  Classical.choose_spec generatedFeasibleRootEightSlot_transport_exists

/-- The chosen transport carries the opposite rooted axis to the opposite first axis. -/
theorem generatedFeasibleRootEightSlotTransport_opposite :
    rhoLocal generatedFeasibleRootEightSlotTransport (conwayShortAxis (Sum.inl (1, 248)) 1) =
      conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1 :=
  generatedFeasibleSixthSlot_local_opposite _ _ _ generatedFeasibleRootEightSlotTransport_first

/-- The chosen transport carries the rooted plus pair axis to Conway's first axis. -/
theorem generatedFeasibleRootEightSlotTransport_conwayAxis :
    rhoLocal generatedFeasibleRootEightSlotTransport (conwayShortAxis (Sum.inl (1, 248)) 0) =
      conwayAxis generatedFeasiblePhysicalRootPair := by
  rw [generatedFeasibleRootEightSlotTransport_first, conwayShortAxis_pair_zero]

/-- The slot-9 feasible prototype: the genuine local image of the counted root-eight
prototype. -/
def generatedFeasibleRootEightSlotPrototype : GriessSpace :=
  rhoLocal generatedFeasibleRootEightSlotTransport generatedFifthRootEightAxis

/-- The prototype lies in the actual H orbit of the counted root-eight prototype. -/
theorem generatedFeasibleRootEightSlotPrototype_mem_rootEight_orbit :
    generatedFeasibleRootEightSlotPrototype ∈ MulAction.orbit H generatedFifthRootEightAxis :=
  ⟨generatedFeasibleRootEightSlotTransport, rfl⟩

/-- The prototype lies in the actual full feasible orbit: the orbit of the opposite axis
under the entire generated stabilizer of the first axis. -/
theorem generatedFeasibleRootEightSlotPrototype_feasible :
    generatedFeasibleRootEightSlotPrototype ∈ generatedFeasibleVectorOrbit
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0)
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1) := by
  have h := generatedFeasibleSixthSlot_orbit_local generatedFeasibleRootEightSlotTransport
    generatedFeasibleRootEightSlot_prototype_feasible
  rwa [generatedFeasibleRootEightSlotTransport_first,
    generatedFeasibleRootEightSlotTransport_opposite] at h

/-- The entire actual A orbit of the prototype consists of genuinely feasible axes. -/
theorem generatedFeasibleRootEightSlot_A_orbit_subset :
    MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
        generatedFeasibleRootEightSlotPrototype ⊆
      generatedFeasibleVectorOrbit
        (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0)
        (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1) := by
  rintro x ⟨g, rfl⟩
  refine generatedFeasibleSixthSlot_orbit_fixed (localIntoGenerated g.val) ?_
    generatedFeasibleRootEightSlotPrototype_feasible
  exact localAxisStabilizer_signedAxis_fixed g.val _ g.property 0

/-- Every actual H fixer of the prototype lies in A, that is, fixes the first axis. -/
theorem generatedFeasibleRootEightSlot_H_stabilizer_le :
    MulAction.stabilizer H generatedFeasibleRootEightSlotPrototype ≤
      localAxisStabilizer generatedFeasiblePhysicalRootPair := by
  intro g hg
  have hg' : rhoLocal g generatedFeasibleRootEightSlotPrototype =
      generatedFeasibleRootEightSlotPrototype := hg
  have hy : generatedFeasibleRootEightSlotTransport⁻¹ * g *
      generatedFeasibleRootEightSlotTransport⁻¹⁻¹ ∈ generatedFifthRootEightLocalAxisStabilizer :=
    generatedFeasibleSixthSlot_conjugate_fixes _ g _ _
      (generatedFeasibleSixthSlot_local_inverse _ rfl) hg'
  have hroot := generatedFeasibleRootEightSlot_stabilizer_fixes_root _ hy 0
  have hc := generatedFeasibleSixthSlot_conjugate_fixes generatedFeasibleRootEightSlotTransport _
    _ _ generatedFeasibleRootEightSlotTransport_conwayAxis hroot
  have he : generatedFeasibleRootEightSlotTransport *
      (generatedFeasibleRootEightSlotTransport⁻¹ * g *
        generatedFeasibleRootEightSlotTransport⁻¹⁻¹) *
        generatedFeasibleRootEightSlotTransport⁻¹ = g := by
    group
  rw [he] at hc
  exact hc

/-- The size-one reduction: under the prototype's entire actual H stabilizer, each signed first
axis forms a singleton orbit. -/
theorem generatedFeasibleRootEightSlot_first_axis_orbit_eq (c : ZMod 2) :
    {z | ∃ g ∈ MulAction.stabilizer H generatedFeasibleRootEightSlotPrototype,
        rhoLocal g (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) c) = z} =
      {conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) c} := by
  ext z
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact Set.mem_singleton_iff.mpr (localAxisStabilizer_signedAxis_fixed g _
      (generatedFeasibleRootEightSlot_H_stabilizer_le hg) c)
  · intro hz
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [Set.mem_singleton_iff.mp hz, map_one]
    rfl

/-- Every genuine local transport of the rooted plus pair axis to the first axis carries the
counted root-eight prototype into the actual A orbit of the chosen prototype. -/
theorem generatedFeasibleRootEightSlot_transport_mem_orbit (k : H)
    (hk : rhoLocal k (conwayShortAxis (Sum.inl (1, 248)) 0) =
      conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) :
    rhoLocal k generatedFifthRootEightAxis ∈
      MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
        generatedFeasibleRootEightSlotPrototype := by
  have hfirst := generatedFeasibleRootEightSlotTransport_conwayAxis
  rw [conwayShortAxis_pair_zero] at hk
  have hA : k * generatedFeasibleRootEightSlotTransport⁻¹ ∈
      localAxisStabilizer generatedFeasiblePhysicalRootPair := by
    change rhoLocal (k * generatedFeasibleRootEightSlotTransport⁻¹)
      (conwayAxis generatedFeasiblePhysicalRootPair) = conwayAxis generatedFeasiblePhysicalRootPair
    rw [map_mul, LinearEquiv.mul_apply, generatedFeasibleSixthSlot_local_inverse _ hfirst, hk]
  refine ⟨⟨k * generatedFeasibleRootEightSlotTransport⁻¹, hA⟩, ?_⟩
  change rhoLocal (k * generatedFeasibleRootEightSlotTransport⁻¹)
    (rhoLocal generatedFeasibleRootEightSlotTransport generatedFifthRootEightAxis) = _
  rw [map_mul, LinearEquiv.mul_apply,
    generatedFeasibleSixthSlot_local_inverse _ (x := generatedFifthRootEightAxis) rfl]

/-- The actual A stabilizer of the prototype. -/
def generatedFeasibleRootEightSlotStabilizer :
    Subgroup (localAxisStabilizer generatedFeasiblePhysicalRootPair) :=
  MulAction.stabilizer (localAxisStabilizer generatedFeasiblePhysicalRootPair)
    generatedFeasibleRootEightSlotPrototype

/-- The entire actual A stabilizer is conjugate to the entire root-eight H stabilizer. -/
def generatedFeasibleRootEightSlotStabilizerEquiv :
    generatedFeasibleRootEightSlotStabilizer ≃* generatedFifthRootEightLocalAxisStabilizer where
  toFun g := by
    refine ⟨generatedFeasibleRootEightSlotTransport⁻¹ * g.val.val *
      generatedFeasibleRootEightSlotTransport, ?_⟩
    have hg : rhoLocal g.val.val generatedFeasibleRootEightSlotPrototype =
        generatedFeasibleRootEightSlotPrototype := g.property
    have hc := generatedFeasibleSixthSlot_conjugate_fixes
      generatedFeasibleRootEightSlotTransport⁻¹ g.val.val _ _
      (generatedFeasibleSixthSlot_local_inverse _ rfl) hg
    rw [inv_inv] at hc
    exact hc
  invFun g := by
    refine ⟨⟨generatedFeasibleRootEightSlotTransport * g.val *
      generatedFeasibleRootEightSlotTransport⁻¹, ?_⟩, ?_⟩
    · exact generatedFeasibleSixthSlot_conjugate_fixes _ _ _ _
        generatedFeasibleRootEightSlotTransport_conwayAxis
        (generatedFeasibleRootEightSlot_stabilizer_fixes_root g.val g.property 0)
    · have hg : rhoLocal g.val generatedFifthRootEightAxis = generatedFifthRootEightAxis :=
        g.property
      exact generatedFeasibleSixthSlot_conjugate_fixes _ _ _ _ rfl hg
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    change generatedFeasibleRootEightSlotTransport *
      (generatedFeasibleRootEightSlotTransport⁻¹ * g.val.val *
        generatedFeasibleRootEightSlotTransport) *
        generatedFeasibleRootEightSlotTransport⁻¹ = g.val.val
    group
  right_inv g := by
    apply Subtype.ext
    change generatedFeasibleRootEightSlotTransport⁻¹ *
      (generatedFeasibleRootEightSlotTransport * g.val *
        generatedFeasibleRootEightSlotTransport⁻¹) *
        generatedFeasibleRootEightSlotTransport = g.val
    group
  map_mul' g k := by
    apply Subtype.ext
    change generatedFeasibleRootEightSlotTransport⁻¹ * (g.val.val * k.val.val) *
        generatedFeasibleRootEightSlotTransport =
      (generatedFeasibleRootEightSlotTransport⁻¹ * g.val.val *
        generatedFeasibleRootEightSlotTransport) *
        (generatedFeasibleRootEightSlotTransport⁻¹ * k.val.val *
          generatedFeasibleRootEightSlotTransport)
    group

/-- The actual A stabilizer of the prototype is its entire actual H stabilizer, since every
H fixer of the prototype lies in A. -/
def generatedFeasibleRootEightSlotStabilizerHEquiv :
    generatedFeasibleRootEightSlotStabilizer ≃*
      MulAction.stabilizer H generatedFeasibleRootEightSlotPrototype where
  toFun g := ⟨g.val.val, g.property⟩
  invFun g := ⟨⟨g.val, generatedFeasibleRootEightSlot_H_stabilizer_le g.property⟩, g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The entire actual A stabilizer of the prototype has exactly 177,408,000 elements. -/
theorem generatedFeasibleRootEightSlotStabilizer_card :
    Nat.card generatedFeasibleRootEightSlotStabilizer = 177408000 := by
  rw [Nat.card_congr generatedFeasibleRootEightSlotStabilizerEquiv.toEquiv]
  exact generatedRootEight_actual_local_stabilizer_card

/-- The prototype's entire actual H stabilizer has exactly 177,408,000 elements. -/
theorem generatedFeasibleRootEightSlot_H_stabilizer_card :
    Nat.card (MulAction.stabilizer H generatedFeasibleRootEightSlotPrototype) = 177408000 := by
  rw [← Nat.card_congr generatedFeasibleRootEightSlotStabilizerHEquiv.toEquiv]
  exact generatedFeasibleRootEightSlotStabilizer_card

/-- The prototype's actual A stabilizer has index 4,000,762,036,224 in A. -/
theorem generatedFeasibleRootEightSlotStabilizer_index :
    generatedFeasibleRootEightSlotStabilizer.index = 4000762036224 := by
  have h := generatedFeasibleRootEightSlotStabilizer.card_mul_index
  rw [generatedFeasibleRootEightSlotStabilizer_card,
    localAxisStabilizer_card_of_co1_card _ co1_card_exact] at h
  omega

/-- Exactly 4,000,762,036,224 original vectors form the slot-9 feasible A orbit. -/
theorem generatedFeasibleRootEightSlot_actual_A_orbit_card :
    Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleRootEightSlotPrototype) = 4000762036224 := by
  have h := generatedFeasibleRootEightSlotStabilizer_index
  rw [generatedFeasibleRootEightSlotStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

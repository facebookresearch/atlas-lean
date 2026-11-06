/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSixthSlotFeasibility
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSixthSlotRootFixation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthLocalOrder

/-! The actual feasible A orbit for source slot 7 (label 6A1) of Höhn–Seysen,
arXiv:2508.01037, Table 3. The counted sixth prototype is transported by a genuine local
element carrying its rooted pair axis to the physical first axis. The entire actual A
stabilizer is identified with the closed sixth H stabilizer, so the A orbit has
9,646,899,200 vectors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A genuine local element carries the positive rooted pair axis to the first axis. -/
theorem generatedFeasibleSixthSlot_transport_exists : ∃ k : H,
    rhoLocal k (conwayShortAxis (Sum.inl (0, generatedSixthTargetPair 0)) 0) =
      conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 :=
  generatedAxis_local_signed_transitive _ _ 0 0

/-- A chosen genuine local transport of the rooted pair axis to the first axis. -/
def generatedFeasibleSixthSlotTransport : H :=
  Classical.choose generatedFeasibleSixthSlot_transport_exists

/-- The chosen transport carries the positive rooted pair axis to the first axis. -/
theorem generatedFeasibleSixthSlotTransport_first :
    rhoLocal generatedFeasibleSixthSlotTransport
      (conwayShortAxis (Sum.inl (0, generatedSixthTargetPair 0)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 :=
  Classical.choose_spec generatedFeasibleSixthSlot_transport_exists

/-- The chosen transport carries the opposite rooted axis to the opposite first axis. -/
theorem generatedFeasibleSixthSlotTransport_opposite :
    rhoLocal generatedFeasibleSixthSlotTransport
      (conwayShortAxis (Sum.inl (0, generatedSixthTargetPair 0)) 1) =
        conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1 :=
  generatedFeasibleSixthSlot_local_opposite _ _ _ generatedFeasibleSixthSlotTransport_first

/-- The slot-7 feasible prototype: the genuine local image of the counted sixth prototype. -/
def generatedFeasibleSixthSlotPrototype : GriessSpace :=
  rhoLocal generatedFeasibleSixthSlotTransport generatedSixthAxis

/-- The prototype lies in the actual H orbit of the counted sixth prototype. -/
theorem generatedFeasibleSixthSlotPrototype_mem_sixth_orbit :
    generatedFeasibleSixthSlotPrototype ∈ MulAction.orbit H generatedSixthAxis :=
  ⟨generatedFeasibleSixthSlotTransport, rfl⟩

/-- The prototype lies in the actual full feasible orbit: the orbit of the opposite axis
under the entire generated stabilizer of the first axis. -/
theorem generatedFeasibleSixthSlotPrototype_feasible :
    generatedFeasibleSixthSlotPrototype ∈ generatedFeasibleVectorOrbit
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0)
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1) := by
  have h := generatedFeasibleSixthSlot_orbit_local generatedFeasibleSixthSlotTransport
    generatedFeasibleSixthSlot_prototype_feasible
  rwa [generatedFeasibleSixthSlotTransport_first,
    generatedFeasibleSixthSlotTransport_opposite] at h

/-- The entire actual A orbit of the prototype consists of genuinely feasible axes. -/
theorem generatedFeasibleSixthSlot_A_orbit_subset :
    MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
        generatedFeasibleSixthSlotPrototype ⊆
      generatedFeasibleVectorOrbit
        (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0)
        (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1) := by
  rintro x ⟨g, rfl⟩
  refine generatedFeasibleSixthSlot_orbit_fixed (localIntoGenerated g.val) ?_
    generatedFeasibleSixthSlotPrototype_feasible
  exact localAxisStabilizer_signedAxis_fixed g.val _ g.property 0

/-- Conjugation by a local transport preserves fixation of transported vectors. -/
theorem generatedFeasibleSixthSlot_conjugate_fixes (h k : H) (x y : GriessSpace)
    (hh : rhoLocal h x = y) (hk : rhoLocal k x = x) :
    rhoLocal (h * k * h⁻¹) y = y := by
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    generatedFeasibleSixthSlot_local_inverse h hh, hk, hh]

/-- Every actual H fixer of the prototype lies in A, that is, fixes the first axis. -/
theorem generatedFeasibleSixthSlot_H_stabilizer_le :
    MulAction.stabilizer H generatedFeasibleSixthSlotPrototype ≤
      localAxisStabilizer generatedFeasiblePhysicalRootPair := by
  intro g hg
  have hg' : rhoLocal g generatedFeasibleSixthSlotPrototype =
      generatedFeasibleSixthSlotPrototype := hg
  have hy : generatedFeasibleSixthSlotTransport⁻¹ * g * generatedFeasibleSixthSlotTransport⁻¹⁻¹ ∈
      generatedSixthLocalAxisStabilizer :=
    generatedFeasibleSixthSlot_conjugate_fixes _ g _ _
      (generatedFeasibleSixthSlot_local_inverse _ rfl) hg'
  have hroot := generatedFeasibleSixthSlot_stabilizer_le_root hy
  change rhoLocal _ (conwayAxis generatedFeasiblePhysicalRootPair) =
    conwayAxis generatedFeasiblePhysicalRootPair
  have hfirst := generatedFeasibleSixthSlotTransport_first
  rw [conwayShortAxis_pair_zero, conwayShortAxis_pair_zero] at hfirst
  have hc := generatedFeasibleSixthSlot_conjugate_fixes generatedFeasibleSixthSlotTransport _ _ _
    hfirst hroot
  have he : generatedFeasibleSixthSlotTransport *
      (generatedFeasibleSixthSlotTransport⁻¹ * g * generatedFeasibleSixthSlotTransport⁻¹⁻¹) *
        generatedFeasibleSixthSlotTransport⁻¹ = g := by
    group
  rw [he] at hc
  exact hc

/-- The proposed size-one reduction: under the prototype's entire actual H stabilizer,
each signed first axis forms a singleton orbit. -/
theorem generatedFeasibleSixthSlot_first_axis_orbit_eq (c : ZMod 2) :
    {z | ∃ g ∈ MulAction.stabilizer H generatedFeasibleSixthSlotPrototype,
        rhoLocal g (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) c) = z} =
      {conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) c} := by
  ext z
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact Set.mem_singleton_iff.mpr (localAxisStabilizer_signedAxis_fixed g _
      (generatedFeasibleSixthSlot_H_stabilizer_le hg) c)
  · intro hz
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [Set.mem_singleton_iff.mp hz, map_one]
    rfl

/-- Every genuine local transport of the rooted pair axis to the first axis carries the counted
sixth prototype into the actual A orbit of the chosen prototype. -/
theorem generatedFeasibleSixthSlot_transport_mem_orbit (k : H)
    (hk : rhoLocal k (conwayShortAxis (Sum.inl (0, generatedSixthTargetPair 0)) 0) =
      conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) :
    rhoLocal k generatedSixthAxis ∈
      MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
        generatedFeasibleSixthSlotPrototype := by
  have hfirst := generatedFeasibleSixthSlotTransport_first
  rw [conwayShortAxis_pair_zero, conwayShortAxis_pair_zero] at hfirst hk
  have hA : k * generatedFeasibleSixthSlotTransport⁻¹ ∈
      localAxisStabilizer generatedFeasiblePhysicalRootPair := by
    change rhoLocal (k * generatedFeasibleSixthSlotTransport⁻¹)
      (conwayAxis generatedFeasiblePhysicalRootPair) = conwayAxis generatedFeasiblePhysicalRootPair
    rw [map_mul, LinearEquiv.mul_apply, generatedFeasibleSixthSlot_local_inverse _ hfirst, hk]
  refine ⟨⟨k * generatedFeasibleSixthSlotTransport⁻¹, hA⟩, ?_⟩
  change rhoLocal (k * generatedFeasibleSixthSlotTransport⁻¹)
    (rhoLocal generatedFeasibleSixthSlotTransport generatedSixthAxis) = _
  rw [map_mul, LinearEquiv.mul_apply,
    generatedFeasibleSixthSlot_local_inverse _ (x := generatedSixthAxis) rfl]

/-- The actual A stabilizer of the prototype. -/
def generatedFeasibleSixthSlotStabilizer :
    Subgroup (localAxisStabilizer generatedFeasiblePhysicalRootPair) :=
  MulAction.stabilizer (localAxisStabilizer generatedFeasiblePhysicalRootPair)
    generatedFeasibleSixthSlotPrototype

/-- The entire actual A stabilizer is conjugate to the entire sixth H stabilizer. -/
def generatedFeasibleSixthSlotStabilizerEquiv :
    generatedFeasibleSixthSlotStabilizer ≃* generatedSixthLocalAxisStabilizer where
  toFun g := by
    refine ⟨generatedFeasibleSixthSlotTransport⁻¹ * g.val.val *
      generatedFeasibleSixthSlotTransport, ?_⟩
    have hg : rhoLocal g.val.val generatedFeasibleSixthSlotPrototype =
        generatedFeasibleSixthSlotPrototype := g.property
    have hc := generatedFeasibleSixthSlot_conjugate_fixes
      generatedFeasibleSixthSlotTransport⁻¹ g.val.val _ _
      (generatedFeasibleSixthSlot_local_inverse _ rfl) hg
    rw [inv_inv] at hc
    exact hc
  invFun g := by
    refine ⟨⟨generatedFeasibleSixthSlotTransport * g.val *
      generatedFeasibleSixthSlotTransport⁻¹, ?_⟩, ?_⟩
    · have hfirst := generatedFeasibleSixthSlotTransport_first
      rw [conwayShortAxis_pair_zero, conwayShortAxis_pair_zero] at hfirst
      exact generatedFeasibleSixthSlot_conjugate_fixes _ _ _ _ hfirst
        (generatedFeasibleSixthSlot_stabilizer_le_root g.property)
    · have hg : rhoLocal g.val generatedSixthAxis = generatedSixthAxis := g.property
      exact generatedFeasibleSixthSlot_conjugate_fixes _ _ _ _ rfl hg
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    change generatedFeasibleSixthSlotTransport *
      (generatedFeasibleSixthSlotTransport⁻¹ * g.val.val * generatedFeasibleSixthSlotTransport) *
        generatedFeasibleSixthSlotTransport⁻¹ = g.val.val
    group
  right_inv g := by
    apply Subtype.ext
    change generatedFeasibleSixthSlotTransport⁻¹ *
      (generatedFeasibleSixthSlotTransport * g.val * generatedFeasibleSixthSlotTransport⁻¹) *
        generatedFeasibleSixthSlotTransport = g.val
    group
  map_mul' g k := by
    apply Subtype.ext
    change generatedFeasibleSixthSlotTransport⁻¹ * (g.val.val * k.val.val) *
        generatedFeasibleSixthSlotTransport =
      (generatedFeasibleSixthSlotTransport⁻¹ * g.val.val * generatedFeasibleSixthSlotTransport) *
        (generatedFeasibleSixthSlotTransport⁻¹ * k.val.val * generatedFeasibleSixthSlotTransport)
    group

/-- The actual A stabilizer of the prototype is its entire actual H stabilizer, since every
H fixer of the prototype lies in A. -/
def generatedFeasibleSixthSlotStabilizerHEquiv :
    generatedFeasibleSixthSlotStabilizer ≃*
      MulAction.stabilizer H generatedFeasibleSixthSlotPrototype where
  toFun g := ⟨g.val.val, g.property⟩
  invFun g := ⟨⟨g.val, generatedFeasibleSixthSlot_H_stabilizer_le g.property⟩, g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The entire actual A stabilizer of the prototype has exactly 73,574,645,760 elements. -/
theorem generatedFeasibleSixthSlotStabilizer_card :
    Nat.card generatedFeasibleSixthSlotStabilizer = 73574645760 := by
  rw [Nat.card_congr generatedFeasibleSixthSlotStabilizerEquiv.toEquiv]
  exact generatedSixth_local_stabilizer_card

/-- The prototype's entire actual H stabilizer has exactly 73,574,645,760 elements. -/
theorem generatedFeasibleSixthSlot_H_stabilizer_card :
    Nat.card (MulAction.stabilizer H generatedFeasibleSixthSlotPrototype) = 73574645760 := by
  rw [← Nat.card_congr generatedFeasibleSixthSlotStabilizerHEquiv.toEquiv]
  exact generatedFeasibleSixthSlotStabilizer_card

/-- The prototype's actual A stabilizer has index 9,646,899,200 in A. -/
theorem generatedFeasibleSixthSlotStabilizer_index :
    generatedFeasibleSixthSlotStabilizer.index = 9646899200 := by
  have h := generatedFeasibleSixthSlotStabilizer.card_mul_index
  rw [generatedFeasibleSixthSlotStabilizer_card,
    localAxisStabilizer_card_of_co1_card _ co1_card_exact] at h
  omega

/-- Exactly 9,646,899,200 original vectors form the slot-7 feasible A orbit. -/
theorem generatedFeasibleSixthSlot_actual_A_orbit_card :
    Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleSixthSlotPrototype) = 9646899200 := by
  have h := generatedFeasibleSixthSlotStabilizer_index
  rw [generatedFeasibleSixthSlotStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

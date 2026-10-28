/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthFlagMonomialFrameCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthFlagMonomialGenerated
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthProjectionIndex

/-! Orbit-stabilizer assembly for actual fourth-flag generation.
The two remaining finite inputs are the genuine permutation count and 63 reachable frame classes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Reachable frame classes and monomial stabilizer elements give a genuine group lower bound. -/
theorem generatedFourthFlagFrames_group_card_le
    (P : Subgroup golayAutomorphismSubgroup) (K : Subgroup leechIsomSubgroup)
    (hs : generatedFourthFlagEqualSignSubgroup ≤ K)
    (hp : ∀ p ∈ P, golayPermutationIsometry p ∈ K)
    (horbit : 63 ≤ Nat.card (MulAction.orbit K
      (leechReduction (leechCoordinateFrameLattice 0)))) :
    63 * (2048 * Nat.card P) ≤ Nat.card K := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let : Finite LeechModTwo := Finite.of_injective
    leechHyperbolicCoordinates leechHyperbolicCoordinates.injective
  let _ := Fintype.ofFinite K
  let _ := Fintype.ofFinite (MulAction.orbit K
    (leechReduction (leechCoordinateFrameLattice 0)))
  let _ := Fintype.ofFinite (MulAction.stabilizer K
    (leechReduction (leechCoordinateFrameLattice 0)))
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group K
    (leechReduction (leechCoordinateFrameLattice 0))
  simp only [← Nat.card_eq_fintype_card] at h
  have hl := Nat.mul_le_mul horbit
    (generatedFourthFlagMonomial_frame_stabilizer_card_le P K hs hp)
  rwa [h] at hl

/-- The counted flag order forces equality once both actual finite lower bounds are proved. -/
theorem generatedFourthFlagGenerator_eq_flag_of_card_lower_bound
    (P : Subgroup golayAutomorphismSubgroup)
    (hP : 11520 ≤ Nat.card P)
    (hp : ∀ p ∈ P, golayPermutationIsometry p ∈ generatedFourthPhysicalFlagGeneratorSubgroup)
    (horbit : 63 ≤ Nat.card (MulAction.orbit generatedFourthPhysicalFlagGeneratorSubgroup
      (leechReduction (leechCoordinateFrameLattice 0)))) :
    generatedFourthPhysicalFlagGeneratorSubgroup = generatedAxisE8ShortFlagStabilizer
      generatedFourthFlagOctad generatedFourthFlagShort := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let K := generatedFourthPhysicalFlagGeneratorSubgroup
  let L := generatedAxisE8ShortFlagStabilizer generatedFourthFlagOctad generatedFourthFlagShort
  have hlo := generatedFourthFlagFrames_group_card_le P K
    generatedFourthFlagGenerator_equal_sign_le hp horbit
  have hbase : 1486356480 ≤ Nat.card K :=
    (Nat.mul_le_mul_left 63 (Nat.mul_le_mul_left 2048 hP)).trans hlo
  have hL : Nat.card L = 1486356480 :=
    generatedAxisE8ShortFlagStabilizer_card _ _ generatedFourth_flag_incident
  let f : K → L := fun x => ⟨x.val, generatedFourthFlagGenerator_le_flag x.property⟩
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (congrArg (fun u : L => u.val) h)
  have hc : Nat.card K = Nat.card L := by
    apply le_antisymm (Nat.card_le_card_of_injective f hf)
    rw [hL]
    exact hbase
  have hsurj := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hc⟩).2
  apply le_antisymm generatedFourthFlagGenerator_le_flag
  intro e he
  obtain ⟨x, hx⟩ := hsurj ⟨e, he⟩
  have hv := congrArg (fun u : L => u.val) hx
  change x.val = e at hv
  rw [← hv]
  exact x.property

/-- The exact permutation count is a sufficient instance of the lower-bound argument. -/
theorem generatedFourthFlagGenerator_eq_flag_of_card_inputs
    (P : Subgroup golayAutomorphismSubgroup)
    (hP : Nat.card P = 11520)
    (hp : ∀ p ∈ P, golayPermutationIsometry p ∈ generatedFourthPhysicalFlagGeneratorSubgroup)
    (horbit : 63 ≤ Nat.card (MulAction.orbit generatedFourthPhysicalFlagGeneratorSubgroup
      (leechReduction (leechCoordinateFrameLattice 0)))) :
    generatedFourthPhysicalFlagGeneratorSubgroup = generatedAxisE8ShortFlagStabilizer
      generatedFourthFlagOctad generatedFourthFlagShort :=
  generatedFourthFlagGenerator_eq_flag_of_card_lower_bound P (by rw [hP]) hp horbit

/-- Full physical flag generation supplies every genuine Co1 stabilizer lift. -/
theorem generatedFourthFlagGenerator_projection_surjective
    (hgen : generatedFourthPhysicalFlagGeneratorSubgroup =
      generatedAxisE8ShortFlagStabilizer generatedFourthFlagOctad generatedFourthFlagShort) :
    Function.Surjective generatedFourthLocalAxisProjection := by
  intro c
  obtain ⟨g, hg, hgc⟩ := c.property
  have hK : g ∈ generatedFourthPhysicalFlagGeneratorSubgroup := by
    rw [hgen]
    exact hg
  have hm := generatedFourth_monomial_flag_generated_le_projection hK
  obtain ⟨h, hh, hproj⟩ := hm
  refine ⟨⟨h, hh⟩, Subtype.ext ?_⟩
  change projH h = c.val
  exact hproj.trans hgc

/-- The actual fourth H orbit count follows from full physical flag generation. -/
theorem generatedFourthFlagGenerator_axis_orbit_card
    (hgen : generatedFourthPhysicalFlagGeneratorSubgroup =
      generatedAxisE8ShortFlagStabilizer generatedFourthFlagOctad generatedFourthFlagShort) :
    Nat.card (MulAction.orbit H generatedFourthAxis) = 1466587938816000 :=
  generatedFourth_local_axis_orbit_card_iff_surjective.mpr
    (generatedFourthFlagGenerator_projection_surjective hgen)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

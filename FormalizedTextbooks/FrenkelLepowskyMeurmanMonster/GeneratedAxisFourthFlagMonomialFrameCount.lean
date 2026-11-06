/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthFlagMonomialSigns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionFrameOrbit

/-! Counting actual monomial elements in a coordinate-frame stabilizer.
The permutation subgroup parameter is later supplied by the genuine flag permutations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Every constructed monomial isometry fixes the actual coordinate-frame reduction class. -/
theorem generatedFourthFlagMonomial_frame_fixed (e : leechIsomSubgroup)
    (he : e ∈ golayMonomialSubgroup) :
    leechModTwoAction e (leechReduction (leechCoordinateFrameLattice 0)) =
      leechReduction (leechCoordinateFrameLattice 0) := by
  have hm : e • leechNormEightAxis ∈
      MulAction.orbit golayMonomialSubgroup leechNormEightAxis :=
    ⟨⟨e, he⟩, rfl⟩
  rw [leech_monomial_orbit_eq_signedFrame] at hm
  obtain ⟨t, ht⟩ := hm
  have h := congrArg (fun u : LeechNormEight => leechReduction u.val) ht
  rw [leechSignedFrame_reduction] at h
  exact h.symm

/-- Actual equal-pair codewords and actual permutations yield distinct physical elements. -/
def generatedFourthFlagMonomialFrameMap
    (P : Subgroup golayAutomorphismSubgroup) (K : Subgroup leechIsomSubgroup)
    (hs : generatedFourthFlagEqualSignSubgroup ≤ K)
    (hp : ∀ p ∈ P, golayPermutationIsometry p ∈ K)
    (a : (generatedFourthFlagPairSignPhase 8 11).ker × P) :
    MulAction.stabilizer K (leechReduction (leechCoordinateFrameLattice 0)) := by
  let d := a.1.val.toAdd
  let e := golayMonomialPair (d, a.2.val)
  have hd : golaySignIsometry d ∈ K := hs ⟨a.1.val, a.1.property, rfl⟩
  have he : e ∈ K := K.mul_mem hd (hp a.2.val a.2.property)
  refine ⟨⟨e, he⟩, ?_⟩
  change leechModTwoAction e (leechReduction (leechCoordinateFrameLattice 0)) = _
  exact generatedFourthFlagMonomial_frame_fixed e ⟨d, a.2.val, rfl⟩

/-- The physical pair parametrization is injective even after restricting both factors. -/
theorem generatedFourthFlagMonomialFrameMap_injective
    (P : Subgroup golayAutomorphismSubgroup) (K : Subgroup leechIsomSubgroup)
    (hs : generatedFourthFlagEqualSignSubgroup ≤ K)
    (hp : ∀ p ∈ P, golayPermutationIsometry p ∈ K) :
    Function.Injective (generatedFourthFlagMonomialFrameMap P K hs hp) := by
  intro a b h
  have he := congrArg (fun u : MulAction.stabilizer K
    (leechReduction (leechCoordinateFrameLattice 0)) => u.val.val) h
  have hab := golayMonomialPair_injective he
  apply Prod.ext
  · apply Subtype.ext
    apply toAdd.injective
    exact congrArg Prod.fst hab
  · apply Subtype.ext
    exact congrArg Prod.snd hab

/-- The actual frame stabilizer contains 2048 distinct sign choices per permutation. -/
theorem generatedFourthFlagMonomial_frame_stabilizer_card_le
    (P : Subgroup golayAutomorphismSubgroup) (K : Subgroup leechIsomSubgroup)
    (hs : generatedFourthFlagEqualSignSubgroup ≤ K)
    (hp : ∀ p ∈ P, golayPermutationIsometry p ∈ K) :
    2048 * Nat.card P ≤
      Nat.card (MulAction.stabilizer K (leechReduction (leechCoordinateFrameLattice 0))) := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  have h := Nat.card_le_card_of_injective
    (generatedFourthFlagMonomialFrameMap P K hs hp)
    (generatedFourthFlagMonomialFrameMap_injective P K hs hp)
  rw [Nat.card_prod, generatedFourthFlagPairSignPhase_kernel_card 8 11 (by decide)] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

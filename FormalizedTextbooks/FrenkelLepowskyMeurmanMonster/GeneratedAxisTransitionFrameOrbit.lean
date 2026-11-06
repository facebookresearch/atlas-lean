/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionFrameClass
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderExact

/-! The actual lattice quotient orbit and its actual frame stabilizer. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000

/-- The actual lattice isometry action on the lattice quotient. -/
noncomputable instance leechFrameClassAction : MulAction leechIsomSubgroup LeechModTwo :=
  MulAction.compHom LeechModTwo leechModTwoAction

/-- Preserving the genuine quotient frame class is exactly the monomial condition. -/
theorem leechFrameClass_stabilizer_eq_monomial :
    MulAction.stabilizer leechIsomSubgroup
      (leechReduction (leechCoordinateFrameLattice 0)) = golayMonomialSubgroup := by
  ext e
  constructor
  · intro he
    have himage : e • leechNormEightAxis ∈ Set.range leechSignedFrame := by
      rw [← leechNormEight_frameClass_eq_signedFrame]
      exact he
    obtain ⟨t, ht⟩ := himage
    obtain ⟨k, hk⟩ := leechSignedFrame_mem_monomial_orbit t
    have hke : k.val • leechNormEightAxis = e • leechNormEightAxis := hk.trans ht
    have hfix : k.val⁻¹ * e ∈ MulAction.stabilizer leechIsomSubgroup leechNormEightAxis := by
      change (k.val⁻¹ * e) • leechNormEightAxis = leechNormEightAxis
      rw [mul_smul, ← hke, inv_smul_smul]
    have hm := golayMonomialSubgroup.mul_mem k.property
      (leechNormEight_stabilizer_le_monomial hfix)
    simpa only [mul_inv_cancel_left] using hm
  · intro he
    have himage : e • leechNormEightAxis ∈ Set.range leechSignedFrame := by
      rw [← leech_monomial_orbit_eq_signedFrame]
      exact ⟨⟨e, he⟩, rfl⟩
    rw [← leechNormEight_frameClass_eq_signedFrame] at himage
    exact himage

/-- The genuine quotient frame orbit contains exactly 8,292,375 classes. -/
theorem leechFrameClass_orbit_card :
    Nat.card (MulAction.orbit leechIsomSubgroup
      (leechReduction (leechCoordinateFrameLattice 0))) = 8292375 := by
  have : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  have : Finite LeechModTwo := Finite.of_injective
    leechHyperbolicCoordinates leechHyperbolicCoordinates.injective
  let _ := Fintype.ofFinite leechIsomSubgroup
  let _ := Fintype.ofFinite (MulAction.orbit leechIsomSubgroup
    (leechReduction (leechCoordinateFrameLattice 0)))
  let _ := Fintype.ofFinite (MulAction.stabilizer leechIsomSubgroup
    (leechReduction (leechCoordinateFrameLattice 0)))
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group leechIsomSubgroup
    (leechReduction (leechCoordinateFrameLattice 0))
  simp only [← Nat.card_eq_fintype_card, leechFrameClass_stabilizer_eq_monomial,
    golayMonomialSubgroup_card] at h
  have hc : Nat.card leechIsomSubgroup = 8315553613086720000 := co0_card_exact
  rw [hc] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 1002795171840) h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

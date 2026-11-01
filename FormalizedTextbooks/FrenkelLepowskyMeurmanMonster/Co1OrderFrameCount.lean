/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact frame stabilizer order and the actual norm-eight orbit counting identity. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderFrameOrbit

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Restricting to the monomial subgroup changes no frame stabilizer elements. -/
def leechFrameStabilizerEquiv :
    MulAction.stabilizer golayMonomialSubgroup leechNormEightAxis ≃
      MulAction.stabilizer leechIsomSubgroup leechNormEightAxis where
  toFun s := ⟨s.val.val, s.property⟩
  invFun s := ⟨⟨s.val, leechNormEight_stabilizer_le_monomial s.property⟩, s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual positive coordinate-frame stabilizer has order 20891566080. -/
theorem leechNormEight_stabilizer_card :
    Nat.card (MulAction.stabilizer leechIsomSubgroup leechNormEightAxis) = 20891566080 := by
  have : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let _ := Fintype.ofFinite golayMonomialSubgroup
  let _ := Fintype.ofFinite (MulAction.orbit golayMonomialSubgroup leechNormEightAxis)
  let _ := Fintype.ofFinite (MulAction.stabilizer golayMonomialSubgroup leechNormEightAxis)
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    golayMonomialSubgroup leechNormEightAxis
  have he : Nat.card (MulAction.stabilizer golayMonomialSubgroup leechNormEightAxis) =
      Nat.card (MulAction.stabilizer leechIsomSubgroup leechNormEightAxis) :=
    Nat.card_congr leechFrameStabilizerEquiv
  simp only [← Nat.card_eq_fintype_card, leech_monomial_frame_orbit_card, he,
    golayMonomialSubgroup_card] at h
  omega

/-- The actual Co₀ order is determined by counting actual norm-eight lattice vectors. -/
theorem leechIsomSubgroup_card_normEight :
    Nat.card leechIsomSubgroup = 20891566080 * Nat.card LeechNormEight := by
  have h := leechNormEight_card_mul_stabilizer
  rw [leechNormEight_stabilizer_card, mul_comm] at h
  exact h.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

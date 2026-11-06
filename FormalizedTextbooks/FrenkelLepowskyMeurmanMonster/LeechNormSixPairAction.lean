/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2PositiveRootStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairCard

/-! The genuine positive-root stabilizer acts on the complete actual paired norm-six catalogue. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every genuine positive-root isometry preserves the actual norm-six paired-vector conditions. -/
theorem leechNormSixPair_action_mem (e : leechRootedA2PositiveRootSubgroup)
    (u : LeechNormSixPair) :
    leechSquareSum (leechIntegralAction e.val.val u.val).val = 48 ∧
      (leechIntegralAction e.val.val u.val).val 0 +
        (leechIntegralAction e.val.val u.val).val 1 = 4 := by
  constructor
  · rw [leechIntegralAction_squareSum]
    exact u.property.1
  · have he : leechIntegralAction e.val.val leechRootedA2Root = leechRootedA2Root :=
      e.property
    have hp := leechRootedA2_integral_pairing_action e.val.val leechRootedA2Root u.val
    rw [he] at hp
    change leechIntegralPairing leechRootedA2RootIntegral _ =
      leechIntegralPairing leechRootedA2RootIntegral _ at hp
    rw [leechRootedA2RootIntegral_pairing, leechRootedA2RootIntegral_pairing,
      u.property.2] at hp
    omega

/-- The original integral isometry action restricted to the actual paired catalogue. -/
instance leechNormSixPairMulAction : MulAction leechRootedA2PositiveRootSubgroup
    LeechNormSixPair where
  smul e u := ⟨leechIntegralAction e.val.val u.val, leechNormSixPair_action_mem e u⟩
  one_smul u := by
    apply Subtype.ext
    change leechIntegralAction 1 u.val = u.val
    rw [map_one]
    rfl
  mul_smul e f u := by
    apply Subtype.ext
    change leechIntegralAction (e.val.val * f.val.val) u.val =
      leechIntegralAction e.val.val (leechIntegralAction f.val.val u.val)
    rw [map_mul, LinearEquiv.mul_apply]

/-- The restricted action retains the original actual lattice vector at every source. -/
theorem leechNormSixPair_smul_val (e : leechRootedA2PositiveRootSubgroup)
    (u : LeechNormSixPair) : (e • u).val = leechIntegralAction e.val.val u.val := rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixActualPairStabilizer

/-! Genuine transports between norm-six vectors paired with any actual fixed norm-four root. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Transporting the actual root to standard coordinates puts each genuinely paired norm-six
vector into the original complete paired catalogue. -/
theorem leechNormSixActualPair_normalized (x y : leechIntegral) (a : leechIsomSubgroup)
    (ha : leechIntegralAction a x = leechRootedA2Root)
    (hy : leechSquareSum y.val = 48) (hp : leechIntegralPairing x.val y.val = 16) :
    leechSquareSum (leechIntegralAction a y).val = 48 ∧
      (leechIntegralAction a y).val 0 + (leechIntegralAction a y).val 1 = 4 := by
  constructor
  · rw [leechIntegralAction_squareSum, hy]
  · have h := leechRootedA2_integral_pairing_action a x y
    rw [ha, hp] at h
    change leechIntegralPairing leechRootedA2RootIntegral _ = 16 at h
    rw [leechRootedA2RootIntegral_pairing] at h
    omega

/-- The genuine Conway point stabilizer of any norm-four root transports all actual norm-six
vectors paired two with it, retaining the fixed root's positive sign. -/
theorem leechNormSixActualPair_transport (x y z : leechIntegral)
    (hx : leechSquareSum x.val = 32)
    (hy : leechSquareSum y.val = 48) (hz : leechSquareSum z.val = 48)
    (hxy : leechIntegralPairing x.val y.val = 16)
    (hxz : leechIntegralPairing x.val z.val = 16) :
    ∃ g : leechIsomSubgroup,
      leechIntegralAction g x = x ∧ leechIntegralAction g y = z := by
  obtain ⟨a, ha⟩ := leechNormSixActualPair_root_transport x hx
  let u : LeechNormSixPair := ⟨leechIntegralAction a y,
    leechNormSixActualPair_normalized x y a ha hy hxy⟩
  let v : LeechNormSixPair := ⟨leechIntegralAction a z,
    leechNormSixActualPair_normalized x z a ha hz hxz⟩
  obtain ⟨e, he⟩ := leechNormSixPair_transitive u v
  have heroot : leechIntegralAction (leechNormSixPairPositiveInclusion e)
      leechRootedA2Root = leechRootedA2Root := e.property
  have hey : leechIntegralAction (leechNormSixPairPositiveInclusion e)
      (leechIntegralAction a y) = leechIntegralAction a z := congrArg Subtype.val he
  refine ⟨a⁻¹ * leechNormSixPairPositiveInclusion e * a, ?_, ?_⟩
  · rw [map_mul, LinearEquiv.mul_apply, map_mul, LinearEquiv.mul_apply, ha, heroot,
      ← ha, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  · rw [map_mul, LinearEquiv.mul_apply, map_mul, LinearEquiv.mul_apply, hey,
      ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl

/-- Actual root-minus-vector remains norm-six and has the same positive root pairing. -/
theorem leechNormSixActualPair_mate (x y : leechIntegral)
    (hx : leechSquareSum x.val = 32) (hy : leechSquareSum y.val = 48)
    (hp : leechIntegralPairing x.val y.val = 16) :
    leechSquareSum (x - y).val = 48 ∧ leechIntegralPairing x.val (x - y).val = 16 := by
  have hxx : leechIntegralPairing x.val x.val = leechSquareSum x.val := by
    simp only [leechIntegralPairing, leechSquareSum, pow_two]
  constructor
  · change leechSquareSum (x.val - y.val) = 48
    rw [leechSquareSum_sub, hx, hy, hp]
    norm_num
  · simp only [Submodule.coe_sub, leechIntegralPairing, Pi.sub_apply, mul_sub,
      Finset.sum_sub_distrib]
    change leechIntegralPairing x.val x.val - leechIntegralPairing x.val y.val = 16
    rw [hxx, hx, hp]
    norm_num

/-- An actual Conway root stabilizer reverses the other distinguished integral line by sending
the norm-six vector to root-minus-vector. -/
theorem leechNormSixActualPair_mate_transport (x y : leechIntegral)
    (hx : leechSquareSum x.val = 32) (hy : leechSquareSum y.val = 48)
    (hp : leechIntegralPairing x.val y.val = 16) :
    ∃ g : leechIsomSubgroup,
      leechIntegralAction g x = x ∧ leechIntegralAction g y = x - y := by
  have hm := leechNormSixActualPair_mate x y hx hy hp
  exact leechNormSixActualPair_transport x y (x - y) hx hy hm.1 hp hm.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

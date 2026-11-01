/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixHS100Flag

/-! The original Conway simultaneous flag stabilizer acts on its actual lattice points. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- Every genuine Conway isometry preserves the complete physical point conditions. -/
theorem leechNormSixHS100PointCondition_action (g : leechIsomSubgroup)
    (x y z : leechIntegral) :
    LeechNormSixHS100PointCondition (leechIntegralAction g x) (leechIntegralAction g y)
      (leechIntegralAction g z) ↔ LeechNormSixHS100PointCondition x y z := by
  rw [LeechNormSixHS100PointCondition, LeechNormSixHS100PointCondition,
    leechIntegralAction_squareSum, leechRootedA2_integral_pairing_action,
    leechRootedA2_integral_pairing_action]

/-- A genuine simultaneous flag stabilizer preserves every original norm-four point. -/
theorem leechNormSixHS100Points_action_mem (x y : leechIntegral)
    (g : leechNormSixActualPairStabilizer x y) (z : LeechNormSixHS100Points x y) :
    LeechNormSixHS100PointCondition x y (leechIntegralAction g.val z.val) := by
  obtain ⟨hx, hy⟩ := (leechNormSixActualPairStabilizer_mem x y g.val).mp g.property
  have h := (leechNormSixHS100PointCondition_action g.val x y z.val).mpr z.property
  rw [hx, hy] at h
  exact h

/-- The actual simultaneous flag subgroup acts through the original integral lattice action. -/
instance leechNormSixHS100PointsMulAction (x y : leechIntegral) :
    MulAction (leechNormSixActualPairStabilizer x y) (LeechNormSixHS100Points x y) where
  smul g z := ⟨leechIntegralAction g.val z.val, leechNormSixHS100Points_action_mem x y g z⟩
  one_smul z := by
    apply Subtype.ext
    change leechIntegralAction 1 z.val = z.val
    rw [map_one]
    rfl
  mul_smul g h z := by
    apply Subtype.ext
    change leechIntegralAction (g.val * h.val) z.val =
      leechIntegralAction g.val (leechIntegralAction h.val z.val)
    rw [map_mul, LinearEquiv.mul_apply]

/-- Every acted-on point retains the entire original physical lattice vector. -/
theorem leechNormSixHS100Points_smul_val (x y : leechIntegral)
    (g : leechNormSixActualPairStabilizer x y) (z : LeechNormSixHS100Points x y) :
    (g • z).val = leechIntegralAction g.val z.val := rfl

/-- The original isometry and its original inverse give an equivalence of genuine point sets. -/
def leechNormSixHS100PointsActionEquiv (g : leechIsomSubgroup) (x y : leechIntegral) :
    LeechNormSixHS100Points x y ≃
      LeechNormSixHS100Points (leechIntegralAction g x) (leechIntegralAction g y) where
  toFun z := ⟨leechIntegralAction g z.val,
    (leechNormSixHS100PointCondition_action g x y z.val).mpr z.property⟩
  invFun z := ⟨leechIntegralAction g⁻¹ z.val, by
    have h := (leechNormSixHS100PointCondition_action g⁻¹
      (leechIntegralAction g x) (leechIntegralAction g y) z.val).mpr z.property
    have hx : leechIntegralAction g⁻¹ (leechIntegralAction g x) = x := by
      rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    have hy : leechIntegralAction g⁻¹ (leechIntegralAction g y) = y := by
      rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [hx, hy] at h
    exact h⟩
  left_inv z := by
    apply Subtype.ext
    change leechIntegralAction g⁻¹ (leechIntegralAction g z.val) = z.val
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv z := by
    apply Subtype.ext
    change leechIntegralAction g (leechIntegralAction g⁻¹ z.val) = z.val
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

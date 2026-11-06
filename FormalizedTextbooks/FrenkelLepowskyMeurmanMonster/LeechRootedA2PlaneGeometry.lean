/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2OrientedNeighbors

/-! Actual standard root and its fixed-point-free neighbor pairing. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The standard integral root 4(e0+e1). -/
def leechRootedA2RootIntegral : Fin 24 → ℤ := fun i =>
  4 * (if i = 0 then 1 else 0) + 4 * (if i = 1 then 1 else 0)

/-- The standard root is in the actual Leech lattice. -/
theorem leechRootedA2RootIntegral_mem : leechRootedA2RootIntegral ∈ leechIntegral := by
  let q : griessCoordinatePairs := ⟨(0, 1), by decide +kernel⟩
  let p := griessCoordinatePairEquiv.symm q
  have hp : griessCoordinatePair p = (0, 1) :=
    congrArg Subtype.val (griessCoordinatePairEquiv.apply_symm_apply q)
  have he : griessShortIntegral (Sum.inl (1, p)) = leechRootedA2RootIntegral := by
    funext i
    simp only [griessShortIntegral, hp, leechRootedA2RootIntegral]
    norm_num
  rw [← he]
  exact griessShortIntegral_mem _

/-- The standard root has integral squared length32. -/
theorem leechRootedA2RootIntegral_squareSum : leechSquareSum leechRootedA2RootIntegral = 32 := by
  decide +kernel

/-- Pairing against the root is exactly four times the two-coordinate sum. -/
theorem leechRootedA2RootIntegral_pairing (v : Fin 24 → ℤ) :
    leechIntegralPairing leechRootedA2RootIntegral v = 4 * (v 0 + v 1) := by
  simp [leechIntegralPairing, leechRootedA2RootIntegral, add_mul, Finset.sum_add_distrib]
  ring

/-- The other oriented neighbor in the same A2 plane is the actual root minus the first. -/
def leechRootedA2NeighborMate (v : leechRootedA2OrientedNeighbor) :
    leechRootedA2OrientedNeighbor :=
  ⟨⟨leechRootedA2RootIntegral - v.val.val,
      leechIntegral.sub_mem leechRootedA2RootIntegral_mem v.val.property⟩,
    by rw [leechSquareSum_sub, leechRootedA2RootIntegral_squareSum, v.property.1,
      leechRootedA2RootIntegral_pairing, v.property.2]; norm_num, by
      change leechRootedA2RootIntegral 0 - v.val.val 0 +
        (leechRootedA2RootIntegral 1 - v.val.val 1) = 4
      have hv := v.property.2
      norm_num [leechRootedA2RootIntegral]
      omega⟩

/-- Subtracting twice restores the original genuine neighbor. -/
theorem leechRootedA2NeighborMate_involutive : Function.Involutive leechRootedA2NeighborMate := by
  intro v
  apply Subtype.ext
  apply Subtype.ext
  change leechRootedA2RootIntegral - (leechRootedA2RootIntegral - v.val.val) = v.val.val
  abel

/-- No actual neighbor is fixed by the root-minus-neighbor operation. -/
theorem leechRootedA2NeighborMate_ne (v : leechRootedA2OrientedNeighbor) :
    leechRootedA2NeighborMate v ≠ v := by
  intro h
  have he := congrArg (fun w : leechRootedA2OrientedNeighbor => w.val.val) h
  change leechRootedA2RootIntegral - v.val.val = v.val.val at he
  have hc : leechRootedA2RootIntegral = v.val.val + v.val.val := by
    exact sub_eq_iff_eq_add.mp he
  have hn := leechRootedA2RootIntegral_squareSum
  rw [hc, leechSquareSum_add] at hn
  have hp : leechIntegralPairing v.val.val v.val.val = leechSquareSum v.val.val := by
    simp only [leechIntegralPairing, leechSquareSum, pow_two]
  rw [hp, v.property.1] at hn
  norm_num at hn

/-- The real A2 coefficient equations have exactly the two genuine neighbor solutions. -/
theorem leechRootedA2Plane_neighbor_coefficients (a b : ℝ)
    (hp : 32 * a + 16 * b = 16)
    (hn : 32 * a ^ 2 + 32 * a * b + 32 * b ^ 2 = 32) :
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = -1) := by
  have hb : b ^ 2 = 1 := by nlinarith [sq_nonneg (2 * a + b - 1)]
  rcases sq_eq_one_iff.mp hb with hb | hb
  · left
    exact ⟨by nlinarith, hb⟩
  · right
    exact ⟨by nlinarith, hb⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

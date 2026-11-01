/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueClassTwoLift
public import Mathlib.LinearAlgebra.BilinearForm.Basic

/-! The faithful commutator coefficient is bilinear on any prescribed binary abelianization map. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The actual binary commutator coefficient on the prescribed abelianization coordinates. -/
def co1ResidueClassTwoPairing (f : V →+ Additive (Abelianization G)) (v w : V) : ZMod 2 :=
  co1ResidueSmallGroupCoefficient (co1ResidueClassTwoBinaryCommutator f v w)

omit [Module (ZMod 2) V] in
/-- Addition in the first coordinate is genuine commutator multiplication. -/
theorem co1ResidueClassTwoPairing_add_left [Finite (commutator G)]
    (hcard : Nat.card (commutator G) ≤ 2) (hcenter : commutator G ≤ Subgroup.center G)
    (f : V →+ Additive (Abelianization G)) (v w t : V) :
    co1ResidueClassTwoPairing f (v + w) t =
      co1ResidueClassTwoPairing f v t + co1ResidueClassTwoPairing f w t := by
  have he := co1ResidueClassTwoBinaryCommutator_image hcenter f (v + w) t
    (co1ResidueClassTwoLift f v * co1ResidueClassTwoLift f w) (co1ResidueClassTwoLift f t)
    (by rw [map_mul, co1ResidueClassTwoLift_image, co1ResidueClassTwoLift_image,
      map_add, toMul_add]) (co1ResidueClassTwoLift_image f t)
  change co1ResidueSmallGroupCoefficient (co1ResidueClassTwoBinaryCommutator f (v + w) t) = _
  rw [he, co1ResidueClassTwoCommutator_mul_left hcenter,
    co1ResidueSmallGroupCoefficient_mul hcard]
  exact add_comm _ _

omit [Module (ZMod 2) V] in
/-- Addition in the second coordinate is genuine commutator multiplication. -/
theorem co1ResidueClassTwoPairing_add_right [Finite (commutator G)]
    (hcard : Nat.card (commutator G) ≤ 2) (hcenter : commutator G ≤ Subgroup.center G)
    (f : V →+ Additive (Abelianization G)) (v w t : V) :
    co1ResidueClassTwoPairing f v (w + t) =
      co1ResidueClassTwoPairing f v w + co1ResidueClassTwoPairing f v t := by
  have he := co1ResidueClassTwoBinaryCommutator_image hcenter f v (w + t)
    (co1ResidueClassTwoLift f v) (co1ResidueClassTwoLift f w * co1ResidueClassTwoLift f t)
    (co1ResidueClassTwoLift_image f v)
    (by rw [map_mul, co1ResidueClassTwoLift_image, co1ResidueClassTwoLift_image,
      map_add, toMul_add])
  change co1ResidueSmallGroupCoefficient (co1ResidueClassTwoBinaryCommutator f v (w + t)) = _
  rw [he, co1ResidueClassTwoCommutator_mul_right hcenter,
    co1ResidueSmallGroupCoefficient_mul hcard]
  rfl

/-- The pairing vanishes on a zero first coordinate. -/
theorem co1ResidueClassTwoPairing_zero_left [Finite (commutator G)]
    (hcard : Nat.card (commutator G) ≤ 2) (hcenter : commutator G ≤ Subgroup.center G)
    (f : V →+ Additive (Abelianization G)) (v : V) : co1ResidueClassTwoPairing f 0 v = 0 := by
  simpa only [zero_add, ZModModule.add_self] using
    co1ResidueClassTwoPairing_add_left hcard hcenter f 0 0 v

/-- The pairing vanishes on a zero second coordinate. -/
theorem co1ResidueClassTwoPairing_zero_right [Finite (commutator G)]
    (hcard : Nat.card (commutator G) ≤ 2) (hcenter : commutator G ≤ Subgroup.center G)
    (f : V →+ Additive (Abelianization G)) (v : V) : co1ResidueClassTwoPairing f v 0 = 0 := by
  simpa only [zero_add, ZModModule.add_self] using
    co1ResidueClassTwoPairing_add_right hcard hcenter f v 0 0

/-- Binary scalars in the first argument are retained exactly. -/
theorem co1ResidueClassTwoPairing_smul_left [Finite (commutator G)]
    (hcard : Nat.card (commutator G) ≤ 2) (hcenter : commutator G ≤ Subgroup.center G)
    (f : V →+ Additive (Abelianization G)) (a : ZMod 2) (v w : V) :
    co1ResidueClassTwoPairing f (a • v) w = a • co1ResidueClassTwoPairing f v w := by
  have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  rcases ha with rfl | rfl
  · simp only [zero_smul, co1ResidueClassTwoPairing_zero_left hcard hcenter]
  · simp only [one_smul]

/-- Binary scalars in the second argument are retained exactly. -/
theorem co1ResidueClassTwoPairing_smul_right [Finite (commutator G)]
    (hcard : Nat.card (commutator G) ≤ 2) (hcenter : commutator G ≤ Subgroup.center G)
    (f : V →+ Additive (Abelianization G)) (a : ZMod 2) (v w : V) :
    co1ResidueClassTwoPairing f v (a • w) = a • co1ResidueClassTwoPairing f v w := by
  have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  rcases ha with rfl | rfl
  · simp only [zero_smul, co1ResidueClassTwoPairing_zero_right hcard hcenter]
  · simp only [one_smul]

/-- The genuine commutator pairing as a binary bilinear form. -/
def co1ResidueClassTwoBilin [Finite (commutator G)]
    (hcard : Nat.card (commutator G) ≤ 2) (hcenter : commutator G ≤ Subgroup.center G)
    (f : V →+ Additive (Abelianization G)) : LinearMap.BilinForm (ZMod 2) V :=
  LinearMap.mk₂ (ZMod 2) (co1ResidueClassTwoPairing f)
    (co1ResidueClassTwoPairing_add_left hcard hcenter f)
    (co1ResidueClassTwoPairing_smul_left hcard hcenter f)
    (co1ResidueClassTwoPairing_add_right hcard hcenter f)
    (co1ResidueClassTwoPairing_smul_right hcard hcenter f)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

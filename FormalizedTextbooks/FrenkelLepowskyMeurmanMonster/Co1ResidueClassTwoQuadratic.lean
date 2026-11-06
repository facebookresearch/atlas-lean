/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueClassTwoBilinear
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! The genuine square coefficient is quadratic, without an assumed classification or splitting. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The square coefficient retains the actual square of a genuine group lift. -/
def co1ResidueClassTwoSquareCoefficient (f : V →+ Additive (Abelianization G)) (v : V) :
    ZMod 2 :=
  co1ResidueSmallGroupCoefficient (co1ResidueClassTwoSquare f v)

/-- The actual square-product identity gives the exact polar companion coefficient. -/
theorem co1ResidueClassTwoSquareCoefficient_add [Finite (commutator G)]
    (hcard : Nat.card (commutator G) ≤ 2) (hcenter : commutator G ≤ Subgroup.center G)
    (f : V →+ Additive (Abelianization G)) (v w : V) :
    co1ResidueClassTwoSquareCoefficient f (v + w) =
      co1ResidueClassTwoSquareCoefficient f v + co1ResidueClassTwoSquareCoefficient f w +
        co1ResidueClassTwoPairing f w v := by
  change co1ResidueSmallGroupCoefficient (co1ResidueClassTwoSquare f (v + w)) = _
  rw [co1ResidueClassTwoSquare_add hcard hcenter,
    co1ResidueSmallGroupCoefficient_mul hcard, co1ResidueSmallGroupCoefficient_mul hcard]
  change co1ResidueClassTwoPairing f w v +
      (co1ResidueClassTwoSquareCoefficient f v + co1ResidueClassTwoSquareCoefficient f w) = _
  ac_rfl

/-- The genuine square coefficient vanishes at zero. -/
theorem co1ResidueClassTwoSquareCoefficient_zero [Finite (commutator G)]
    (hcard : Nat.card (commutator G) ≤ 2) (hcenter : commutator G ≤ Subgroup.center G)
    (f : V →+ Additive (Abelianization G)) : co1ResidueClassTwoSquareCoefficient f 0 = 0 := by
  simpa only [zero_add, co1ResidueClassTwoPairing_zero_left hcard hcenter,
    add_zero, ZModModule.add_self] using
    co1ResidueClassTwoSquareCoefficient_add hcard hcenter f 0 0

/-- The actual square coefficient and actual commutator companion form a binary quadratic map. -/
def co1ResidueClassTwoQuadratic [Finite (commutator G)]
    (hcard : Nat.card (commutator G) ≤ 2) (hcenter : commutator G ≤ Subgroup.center G)
    (f : V →+ Additive (Abelianization G)) : QuadraticMap (ZMod 2) V (ZMod 2) where
  toFun := co1ResidueClassTwoSquareCoefficient f
  toFun_smul a v := by
    have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    rcases ha with rfl | rfl
    · simp only [zero_smul, zero_mul, co1ResidueClassTwoSquareCoefficient_zero hcard hcenter]
    · simp only [one_smul, one_mul]
  exists_companion' := ⟨(co1ResidueClassTwoBilin hcard hcenter f).flip,
    co1ResidueClassTwoSquareCoefficient_add hcard hcenter f⟩

/-- An original involutory group element has zero square coefficient at its coordinates. -/
theorem co1ResidueClassTwoQuadratic_of_involution [Finite (commutator G)]
    (hcard : Nat.card (commutator G) ≤ 2) (hcenter : commutator G ≤ Subgroup.center G)
    (f : V →+ Additive (Abelianization G)) (v : V) (x : G)
    (hx : Abelianization.of x = (f v).toMul) (hsquare : x * x = 1) :
    co1ResidueClassTwoQuadratic hcard hcenter f v = 0 := by
  have he : co1ResidueClassTwoSquare f v = 1 := by
    apply Subtype.ext
    rw [co1ResidueClassTwoSquare_image hcard hcenter f v x hx, pow_two, hsquare]
    rfl
  change co1ResidueSmallGroupCoefficient (co1ResidueClassTwoSquare f v) = 0
  rw [he, co1ResidueSmallGroupCoefficient_one]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

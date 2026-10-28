/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueClassTwoCommutators

/-! Chosen lifts of an actual additive abelianization map, with exact square
and commutator images. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped commutatorElement
set_option backward.isDefEq.respectTransparency false

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- A chosen genuine group lift of the prescribed actual abelianization image. -/
def co1ResidueClassTwoLift (f : V →+ Additive (Abelianization G)) (v : V) : G :=
  Classical.choose (QuotientGroup.mk'_surjective (commutator G) (f v).toMul)

omit [Module (ZMod 2) V] in
/-- Each chosen group lift has exactly the prescribed abelianization image. -/
theorem co1ResidueClassTwoLift_image (f : V →+ Additive (Abelianization G)) (v : V) :
    Abelianization.of (co1ResidueClassTwoLift f v) = (f v).toMul :=
  Classical.choose_spec (QuotientGroup.mk'_surjective (commutator G) (f v).toMul)

/-- The square of a binary lift belongs to the actual commutator group. -/
theorem co1ResidueClassTwoLift_square_mem (f : V →+ Additive (Abelianization G)) (v : V) :
    co1ResidueClassTwoLift f v ^ 2 ∈ commutator G := by
  rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_pow, co1ResidueClassTwoLift_image]
  have h : f v + f v = 0 := by rw [← map_add, ZModModule.add_self, map_zero]
  simpa only [pow_two, toMul_add, toMul_zero] using
    congrArg Additive.toMul h

/-- The square of a chosen lift, retained as an actual commutator-subgroup element. -/
def co1ResidueClassTwoSquare (f : V →+ Additive (Abelianization G)) (v : V) : commutator G :=
  ⟨co1ResidueClassTwoLift f v ^ 2, co1ResidueClassTwoLift_square_mem f v⟩

/-- The actual commutator of two chosen group lifts. -/
def co1ResidueClassTwoBinaryCommutator (f : V →+ Additive (Abelianization G)) (v w : V) :
    commutator G :=
  co1ResidueClassTwoCommutator (co1ResidueClassTwoLift f v) (co1ResidueClassTwoLift f w)

/-- Square images are independent of the chosen genuine lift. -/
theorem co1ResidueClassTwoSquare_image [Finite (commutator G)]
    (hcard : Nat.card (commutator G) ≤ 2) (hcenter : commutator G ≤ Subgroup.center G)
    (f : V →+ Additive (Abelianization G)) (v : V) (x : G)
    (hx : Abelianization.of x = (f v).toMul) :
    (co1ResidueClassTwoSquare f v).val = x ^ 2 :=
  co1ResidueClassTwo_square_invariant hcard hcenter _ x
    ((co1ResidueClassTwoLift_image f v).trans hx.symm)

omit [Module (ZMod 2) V] in
/-- Commutator images depend only on the two prescribed abelianization images. -/
theorem co1ResidueClassTwoBinaryCommutator_image
    (hcenter : commutator G ≤ Subgroup.center G)
    (f : V →+ Additive (Abelianization G)) (v w : V) (x y : G)
    (hx : Abelianization.of x = (f v).toMul)
    (hy : Abelianization.of y = (f w).toMul) :
    co1ResidueClassTwoBinaryCommutator f v w = co1ResidueClassTwoCommutator x y := by
  calc
    _ = co1ResidueClassTwoCommutator x (co1ResidueClassTwoLift f w) :=
      co1ResidueClassTwoCommutator_invariant_left hcenter _ x _
        ((co1ResidueClassTwoLift_image f v).trans hx.symm)
    _ = co1ResidueClassTwoCommutator x y :=
      co1ResidueClassTwoCommutator_invariant_right hcenter _ y x
        ((co1ResidueClassTwoLift_image f w).trans hy.symm)

/-- The exact square-product formula on the prescribed binary coordinates. -/
theorem co1ResidueClassTwoSquare_add [Finite (commutator G)]
    (hcard : Nat.card (commutator G) ≤ 2) (hcenter : commutator G ≤ Subgroup.center G)
    (f : V →+ Additive (Abelianization G)) (v w : V) :
    co1ResidueClassTwoSquare f (v + w) =
      co1ResidueClassTwoBinaryCommutator f w v *
        (co1ResidueClassTwoSquare f v * co1ResidueClassTwoSquare f w) := by
  apply Subtype.ext
  change (co1ResidueClassTwoSquare f (v + w)).val =
    ⁅co1ResidueClassTwoLift f w, co1ResidueClassTwoLift f v⁆ *
      (co1ResidueClassTwoLift f v ^ 2 * co1ResidueClassTwoLift f w ^ 2)
  rw [co1ResidueClassTwoSquare_image hcard hcenter f (v + w)
    (co1ResidueClassTwoLift f v * co1ResidueClassTwoLift f w)]
  · exact co1ResidueClassTwo_mul_square hcenter _ _
  · rw [map_mul, co1ResidueClassTwoLift_image, co1ResidueClassTwoLift_image, map_add]
    rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueClassTwoSquares
public import Mathlib.Algebra.Module.ZMod

/-! An involution-generated group has an actual characteristic-two abelianization. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Original involution generators force exponent two in the actual abelianization. -/
theorem co1ResidueClassTwo_abelianization_square {G I : Type*} [Group G]
    (phi : I → G) (hsquare : ∀ i, phi i * phi i = 1)
    (hgen : Subgroup.closure (Set.range phi) = ⊤) (x : G) :
    (Abelianization.of x) ^ 2 = 1 := by
  have hx : x ∈ Subgroup.closure (Set.range phi) := by rw [hgen]; trivial
  refine Subgroup.closure_induction (p := fun y _ => (Abelianization.of y) ^ 2 = 1)
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    rw [pow_two, ← map_mul, hsquare i, map_one]
  · simp
  · intro a b _ _ ha hb
    rw [map_mul, mul_pow, ha, hb, one_mul]
  · intro a _ ha
    rw [map_inv, inv_pow, ha, inv_one]

/-- The actual additive abelianization is killed by the integer two. -/
theorem co1ResidueClassTwo_abelianization_two_nsmul {G I : Type*} [Group G]
    (phi : I → G) (hsquare : ∀ i, phi i * phi i = 1)
    (hgen : Subgroup.closure (Set.range phi) = ⊤)
    (x : Additive (Abelianization G)) : 2 • x = 0 := by
  have hs : Function.Surjective (Abelianization.of : G → Abelianization G) :=
    QuotientGroup.mk'_surjective (commutator G)
  obtain ⟨g, hg⟩ := hs x.toMul
  have h := co1ResidueClassTwo_abelianization_square phi hsquare hgen g
  rw [hg] at h
  exact congrArg Additive.ofMul h

/-- The canonical binary scalar structure on the actual involution-generated abelianization. -/
abbrev co1ResidueClassTwoAbelianModule {G I : Type*} [Group G]
    (phi : I → G) (hsquare : ∀ i, phi i * phi i = 1)
    (hgen : Subgroup.closure (Set.range phi) = ⊤) :
    Module (ZMod 2) (Additive (Abelianization G)) :=
  AddCommGroup.zmodModule (co1ResidueClassTwo_abelianization_two_nsmul phi hsquare hgen)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

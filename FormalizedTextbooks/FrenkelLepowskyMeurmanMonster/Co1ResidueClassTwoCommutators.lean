/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueClassTwoAbelianization

/-! Actual commutators and their faithful binary coefficients in a group of class at most two. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped commutatorElement
set_option backward.isDefEq.respectTransparency false

/-- The actual commutator as an element of the actual derived subgroup. -/
def co1ResidueClassTwoCommutator {G : Type*} [Group G] (x y : G) : commutator G :=
  ⟨⁅x, y⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)⟩

/-- In a group of class at most two, commutators multiply in their first entry. -/
theorem co1ResidueClassTwoCommutator_mul_left {G : Type*} [Group G]
    (hcenter : commutator G ≤ Subgroup.center G) (x y z : G) :
    co1ResidueClassTwoCommutator (x * y) z =
      co1ResidueClassTwoCommutator y z * co1ResidueClassTwoCommutator x z := by
  apply Subtype.ext
  change ⁅x * y, z⁆ = ⁅y, z⁆ * ⁅x, z⁆
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hc := Subgroup.mem_center_iff.mp
    (hcenter (co1ResidueClassTwoCommutator y z).property) x
  change x * ⁅y, z⁆ = ⁅y, z⁆ * x at hc
  rw [hc]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

/-- In a group of class at most two, commutators multiply in their second entry. -/
theorem co1ResidueClassTwoCommutator_mul_right {G : Type*} [Group G]
    (hcenter : commutator G ≤ Subgroup.center G) (x y z : G) :
    co1ResidueClassTwoCommutator x (y * z) =
      co1ResidueClassTwoCommutator x y * co1ResidueClassTwoCommutator x z := by
  apply Subtype.ext
  change ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆
  rw [commutatorElement_mul_right_eq_mul_conj]
  have hc := Subgroup.mem_center_iff.mp
    (hcenter (co1ResidueClassTwoCommutator x z).property) y
  change y * ⁅x, z⁆ = ⁅x, z⁆ * y at hc
  rw [mul_assoc (⁅x, y⁆) y (⁅x, z⁆), hc]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

/-- The first commutator entry is determined by its actual abelianization class. -/
theorem co1ResidueClassTwoCommutator_invariant_left {G : Type*} [Group G]
    (hcenter : commutator G ≤ Subgroup.center G) (x y z : G)
    (hxy : Abelianization.of x = Abelianization.of y) :
    co1ResidueClassTwoCommutator x z = co1ResidueClassTwoCommutator y z :=
  Subtype.ext (co1ResidueClassTwo_commutator_left_invariant hcenter x y z hxy)

/-- The second commutator entry is determined by its actual abelianization class. -/
theorem co1ResidueClassTwoCommutator_invariant_right {G : Type*} [Group G]
    (hcenter : commutator G ≤ Subgroup.center G) (x y z : G)
    (hxy : Abelianization.of x = Abelianization.of y) :
    co1ResidueClassTwoCommutator z x = co1ResidueClassTwoCommutator z y := by
  apply Subtype.ext
  change ⁅z, x⁆ = ⁅z, y⁆
  rw [← commutatorElement_inv x z, ← commutatorElement_inv y z,
    co1ResidueClassTwo_commutator_left_invariant hcenter x y z hxy]

/-- Faithful binary coefficients convert actual commutator multiplication to addition. -/
theorem co1ResidueClassTwo_commutator_coefficient_mul {G : Type*} [Group G]
    [Finite (commutator G)] (hcard : Nat.card (commutator G) ≤ 2)
    (c d : commutator G) :
    co1ResidueSmallGroupCoefficient (c * d) =
      co1ResidueSmallGroupCoefficient c + co1ResidueSmallGroupCoefficient d :=
  co1ResidueSmallGroupCoefficient_mul hcard c d

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

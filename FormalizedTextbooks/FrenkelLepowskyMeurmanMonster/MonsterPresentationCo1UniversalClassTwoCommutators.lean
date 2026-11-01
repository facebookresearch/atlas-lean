/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Original source commutators descend bilinearly through the exact binary quotient. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalClassTwoCenter

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped commutatorElement
set_option backward.isDefEq.respectTransparency false

/-- The original source commutator as an element of its actual commutator subgroup. -/
def co1UniversalCommutator (x y : Co1UniversalPresentation) :
    commutator Co1UniversalPresentation :=
  ⟨⁅x, y⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)⟩

/-- Every bounded source commutator is fixed by all inner source conjugations. -/
theorem co1Universal_commutator_conj_eq
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (c : commutator Co1UniversalPresentation) (g : Co1UniversalPresentation) :
    g * c.val * g⁻¹ = c.val := by
  have hz := co1Universal_commutator_le_center_of_card_le_two hfinite hcard c.property
  rw [Subgroup.mem_center_iff.mp hz g, mul_assoc, mul_inv_cancel, mul_one]

/-- The bounded source commutator is multiplicative in its first source argument. -/
theorem co1UniversalCommutator_mul_left
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (x y z : Co1UniversalPresentation) :
    co1UniversalCommutator (x * y) z =
      co1UniversalCommutator y z * co1UniversalCommutator x z := by
  apply Subtype.ext
  change ⁅x * y, z⁆ = ⁅y, z⁆ * ⁅x, z⁆
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hconj := co1Universal_commutator_conj_eq hfinite hcard
    (co1UniversalCommutator y z) x
  change x * ⁅y, z⁆ * x⁻¹ = ⁅y, z⁆ at hconj
  rw [hconj]

/-- The bounded source commutator is multiplicative in its second source argument. -/
theorem co1UniversalCommutator_mul_right
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (x y z : Co1UniversalPresentation) :
    co1UniversalCommutator x (y * z) =
      co1UniversalCommutator x y * co1UniversalCommutator x z := by
  apply Subtype.ext
  change ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆
  calc
    ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
      rw [commutatorElement_mul_right_eq_mul_conj]
      simp only [mul_assoc]
    _ = ⁅x, y⁆ * ⁅x, z⁆ := by
      have hconj := co1Universal_commutator_conj_eq hfinite hcard
        (co1UniversalCommutator x z) y
      change y * ⁅x, z⁆ * y⁻¹ = ⁅x, z⁆ at hconj
      rw [hconj]

/-- Equal actual binary coordinates have source ratio in exactly the source commutator. -/
theorem co1Universal_binary_ratio_mem_commutator (x y : Co1UniversalPresentation)
    (hxy : co1UniversalIntoBinary x = co1UniversalIntoBinary y) :
    x⁻¹ * y ∈ commutator Co1UniversalPresentation := by
  rw [← co1UniversalIntoBinary_ker]
  change co1UniversalIntoBinary (x⁻¹ * y) = 1
  rw [map_mul, map_inv, hxy, inv_mul_cancel]

/-- The first source commutator argument depends only on its exact actual binary coordinate. -/
theorem co1UniversalCommutator_eq_of_binary_eq_left
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (x y z : Co1UniversalPresentation) (hxy : co1UniversalIntoBinary x = co1UniversalIntoBinary y) :
    co1UniversalCommutator x z = co1UniversalCommutator y z := by
  let c := x⁻¹ * y
  have hc := co1Universal_binary_ratio_mem_commutator x y hxy
  have hz := co1Universal_commutator_le_center_of_card_le_two hfinite hcard hc
  have hm : Commute c z := (Subgroup.mem_center_iff.mp hz z).symm
  have he : co1UniversalCommutator c z = 1 :=
    Subtype.ext (commutatorElement_eq_one_iff_commute.mpr hm)
  have hy : y = x * c := by simp only [c, mul_inv_cancel_left]
  rw [hy, co1UniversalCommutator_mul_left hfinite hcard, he, one_mul]

/-- The second source commutator argument depends only on its exact actual binary coordinate. -/
theorem co1UniversalCommutator_eq_of_binary_eq_right
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (x y z : Co1UniversalPresentation) (hyz : co1UniversalIntoBinary y = co1UniversalIntoBinary z) :
    co1UniversalCommutator x y = co1UniversalCommutator x z := by
  let c := y⁻¹ * z
  have hc := co1Universal_binary_ratio_mem_commutator y z hyz
  have hz := co1Universal_commutator_le_center_of_card_le_two hfinite hcard hc
  have hm : Commute x c := Subgroup.mem_center_iff.mp hz x
  have he : co1UniversalCommutator x c = 1 :=
    Subtype.ext (commutatorElement_eq_one_iff_commute.mpr hm)
  have hz' : z = y * c := by simp only [c, mul_inv_cancel_left]
  rw [hz', co1UniversalCommutator_mul_right hfinite hcard, he, mul_one]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

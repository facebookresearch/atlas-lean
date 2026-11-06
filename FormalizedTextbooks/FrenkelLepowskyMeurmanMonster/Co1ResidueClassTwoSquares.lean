/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueSmallGroup
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Tactic.Group

/-! Generic source-faithful square identities for central commutator groups of order at most two. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped commutatorElement
set_option backward.isDefEq.respectTransparency false

/-- Centrality gives the exact square-product identity, with its full commutator factor. -/
theorem co1ResidueClassTwo_mul_square {G : Type*} [Group G]
    (hcenter : commutator G ≤ Subgroup.center G) (x y : G) :
    (x * y) ^ 2 = ⁅y, x⁆ * (x ^ 2 * y ^ 2) := by
  have hz := hcenter (Subgroup.commutator_mem_commutator
    (Subgroup.mem_top y) (Subgroup.mem_top x))
  have hc := Subgroup.mem_center_iff.mp hz x
  change x * ⁅y, x⁆ = ⁅y, x⁆ * x at hc
  have he : y * x = ⁅y, x⁆ * x * y := by
    simp [commutatorElement_def, mul_assoc]
  calc
    (x * y) ^ 2 = x * (y * x) * y := by simp only [pow_two, mul_assoc]
    _ = x * (⁅y, x⁆ * x * y) * y := by rw [he]
    _ = ((x * ⁅y, x⁆) * x) * y * y := by simp only [mul_assoc]
    _ = ((⁅y, x⁆ * x) * x) * y * y := by rw [hc]
    _ = ⁅y, x⁆ * (x ^ 2 * y ^ 2) := by simp only [pow_two, mul_assoc]

/-- Equal abelianization images differ by an actual commutator-group element. -/
theorem co1ResidueClassTwo_difference_mem {G : Type*} [Group G] (x y : G)
    (hxy : Abelianization.of x = Abelianization.of y) : x * y⁻¹ ∈ commutator G := by
  rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]

/-- Squares depend only on the abelianization image when the central commutator
has order at most two. -/
theorem co1ResidueClassTwo_square_invariant {G : Type*} [Group G] [Finite (commutator G)]
    (hcard : Nat.card (commutator G) ≤ 2) (hcenter : commutator G ≤ Subgroup.center G)
    (x y : G) (hxy : Abelianization.of x = Abelianization.of y) : x ^ 2 = y ^ 2 := by
  let k := x * y⁻¹
  have hk : k ∈ commutator G := co1ResidueClassTwo_difference_mem x y hxy
  have hs : k * k = 1 := congrArg Subtype.val
    (co1ResidueSmallGroup_square hcard (⟨k, hk⟩ : commutator G))
  have hc : Commute k y := by
    change k * y = y * k
    exact (Subgroup.mem_center_iff.mp (hcenter hk) y).symm
  have he : x = k * y := by simp [k, mul_assoc]
  rw [he, hc.mul_pow, pow_two, hs, one_mul]

/-- Actual commutators also depend only on each entry's abelianization class. -/
theorem co1ResidueClassTwo_commutator_left_invariant {G : Type*} [Group G]
    (hcenter : commutator G ≤ Subgroup.center G) (x y z : G)
    (hxy : Abelianization.of x = Abelianization.of y) : ⁅x, z⁆ = ⁅y, z⁆ := by
  let k := x * y⁻¹
  have hk : k ∈ commutator G := co1ResidueClassTwo_difference_mem x y hxy
  have hc : Commute k z := by
    change k * z = z * k
    exact (Subgroup.mem_center_iff.mp (hcenter hk) z).symm
  have he : x = k * y := by simp [k, mul_assoc]
  rw [he, commutatorElement_mul_left_eq_conj_mul, hc.commutator_eq, mul_one]
  have hh : Commute k ⁅y, z⁆ := by
    change k * ⁅y, z⁆ = ⁅y, z⁆ * k
    exact (Subgroup.mem_center_iff.mp (hcenter hk) ⁅y, z⁆).symm
  exact hh.mul_inv_cancel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

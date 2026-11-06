/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2MonomialOrbits

/-! Exact preservation of the genuine short catalogue families by monomial isometries. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual integral image represents the permuted short label with one of its two signs. -/
theorem leechRootedA2_short_integral_image (e : leechIsomSubgroup) (r : GriessShortIndex) :
    leechIntegralAction e (griessShortLatticeVector r) =
        griessShortLatticeVector (griessShortPermutation e r) ∨
    leechIntegralAction e (griessShortLatticeVector r) =
        -griessShortLatticeVector (griessShortPermutation e r) := by
  apply leechShort_same_class
  · rw [leechIntegralAction_squareSum]
    exact griessShortIntegral_squareSum r
  · exact griessShortIntegral_squareSum _
  · exact (griessShortPermutation_class e r).symm

/-- Physical coordinate squares of an actual monomial image are permuted without alteration. -/
theorem leechRootedA2_monomial_square (d : golayCode) (p : golayAutomorphismSubgroup)
    (u : leechIntegral) (i : Fin 24) :
    (leechIntegralAction (golaySignIsometry d * golayPermutationIsometry p) u).val
      (p.val i) ^ 2 = u.val i ^ 2 := by
  rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
    leechIntegralAction_golayPermutation]
  simp only [golayIntegerSign, golayIntegerPermute, p.val.symm_apply_apply]
  split_ifs <;> simp only [neg_sq]

/-- The original three catalogue families can be distinguished by coordinate squares,
independently of a coordinate permutation. -/
theorem leechRootedA2_family_of_squares (r s : GriessShortIndex) (p : Equiv.Perm (Fin 24))
    (h : ∀ i, griessShortIntegral r i ^ 2 = griessShortIntegral s (p i) ^ 2) :
    leechRootedA2NeighborFamily r = leechRootedA2NeighborFamily s := by
  rcases r with ⟨a, u⟩ | (⟨b, v⟩ | ⟨c, w⟩) <;>
    rcases s with ⟨d, x⟩ | (⟨e, y⟩ | ⟨f, z⟩)
  · rfl
  · have hh := h (griessCoordinatePair u).1
    rw [griessPair_first] at hh
    have hl := griessOctad_coordinate_square_le e y (p (griessCoordinatePair u).1)
    nlinarith
  · have hh := h (griessCoordinatePair u).1
    rw [griessPair_first] at hh
    have hl := griessOdd_coordinate_square_le f z (p (griessCoordinatePair u).1)
    nlinarith
  · have hh := h (p.symm (griessCoordinatePair x).1)
    rw [p.apply_symm_apply, griessPair_first] at hh
    have hl := griessOctad_coordinate_square_le b v (p.symm (griessCoordinatePair x).1)
    nlinarith
  · rfl
  · have hh := h (golayOctadCoordinate b 0)
    rw [griessOctad_coordinate_square_local, griessOdd_coordinate_square] at hh
    split_ifs at hh <;> norm_num at hh
  · have hh := h (p.symm (griessCoordinatePair x).1)
    rw [p.apply_symm_apply, griessPair_first] at hh
    have hl := griessOdd_coordinate_square_le c w (p.symm (griessCoordinatePair x).1)
    nlinarith
  · have hh := h (p.symm (golayOctadCoordinate e 0))
    rw [p.apply_symm_apply, griessOctad_coordinate_square_local,
      griessOdd_coordinate_square] at hh
    split_ifs at hh <;> norm_num at hh
  · rfl

/-- Every genuine Golay monomial isometry preserves each original short-vector family. -/
theorem leechRootedA2_monomial_preserves_family (e : leechIsomSubgroup)
    (he : e ∈ golayMonomialSubgroup) (r : GriessShortIndex) :
    leechRootedA2NeighborFamily (griessShortPermutation e r) =
      leechRootedA2NeighborFamily r := by
  obtain ⟨d, p, rfl⟩ := he
  symm
  apply leechRootedA2_family_of_squares r _ p.val
  intro i
  have hs := leechRootedA2_monomial_square d p (griessShortLatticeVector r) i
  rcases leechRootedA2_short_integral_image
      (golaySignIsometry d * golayPermutationIsometry p) r with hi | hi
  · rw [hi] at hs
    exact hs.symm
  · rw [hi] at hs
    simpa only [Submodule.coe_neg, Pi.neg_apply, neg_sq, griessShortLatticeVector] using hs.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

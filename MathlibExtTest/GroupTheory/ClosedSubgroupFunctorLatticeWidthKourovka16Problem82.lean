/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.ClosedSubgroupFunctorLatticeWidthKourovka16Problem82
import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace MathlibExt.GroupTheory.ClosedSubgroupFunctorLatticeWidthKourovka16Problem82Wanted.Test

private def twoThreeGroups : FiniteGroupClass := fun G _ _ ↦
  ∀ p : ℕ, p.Prime → p ∣ Nat.card G → p ∈ ({2, 3} : Set ℕ)

private theorem dihedral_mem : twoThreeGroups (DihedralGroup 3) := by
  intro p hp hd
  rw [DihedralGroup.nat_card] at hd
  exact (hp.dvd_mul.mp hd).imp (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp

private theorem closed_twoThreeGroups : IsClosedClass twoThreeGroups := by
  refine ⟨⟨DihedralGroup 3, inferInstance, inferInstance, dihedral_mem⟩, ?_, ?_, ?_⟩
  · intro G H _ _ _ _ f hf hG p hp hd
    exact hG p hp (hd.trans (Subgroup.card_dvd_of_surjective hf))
  · intro G _ _ H hG p hp hd
    exact hG p hp (hd.trans H.card_subgroup_dvd_card)
  · intro G H _ _ _ _ hG hH p hp hd
    rw [Nat.card_prod] at hd
    exact (hp.dvd_mul.mp hd).elim (hG p hp) (hH p hp)

-- The dihedral group of order six realizes both primes in the class.
private theorem prime_support : primesOf twoThreeGroups = {2, 3} := by
  ext p
  constructor
  · rintro ⟨hp, G, _, _, hG, hd⟩
    exact hG p hp hd
  · rintro (rfl | h)
    · exact ⟨Nat.prime_two, DihedralGroup 3, inferInstance, inferInstance, dihedral_mem,
        by rw [DihedralGroup.nat_card]; decide⟩
    · obtain rfl : p = 3 := h
      exact ⟨Nat.prime_three, DihedralGroup 3, inferInstance, inferInstance, dihedral_mem,
        by rw [DihedralGroup.nat_card]; decide⟩

-- Two available primes already force an antichain of more than two functors in this class.
example : ∃ A : Set SubgroupAssignment, (∀ τ ∈ A, IsClosedSubgroupFunctor twoThreeGroups τ) ∧
    (∀ τ₁ ∈ A, ∀ τ₂ ∈ A, τ₁ ≠ τ₂ → ¬ FunctorLE twoThreeGroups τ₁ τ₂) ∧ 2 < Cardinal.mk A := by
  by_contra h
  apply existsNonnilpotentClassOfSmallWidth_refuted
  refine ⟨twoThreeGroups, closed_twoThreeGroups, ?_, ?_⟩
  · refine ⟨DihedralGroup 3, inferInstance, inferInstance, dihedral_mem, fun hn ↦ ?_⟩
    exact Group.IsNilpotent.center_ne_bot _ (DihedralGroup.center_eq_bot_of_odd_ne_one
      (by decide : Odd 3) (by decide))
  · intro A hc ha
    have hcard : Cardinal.mk A ≤ 2 := le_of_not_gt fun hlt ↦ h ⟨A, hc, ha, hlt⟩
    simpa [prime_support, Cardinal.mk_insert, Cardinal.mk_singleton] using hcard

end MathlibExt.GroupTheory.ClosedSubgroupFunctorLatticeWidthKourovka16Problem82Wanted.Test

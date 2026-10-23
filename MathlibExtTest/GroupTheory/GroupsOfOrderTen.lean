/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.GroupsOfOrderTen

import Mathlib.Tactic

namespace MathlibExtTest.GroupTheory.GroupsOfOrderTen

open _root_.GroupsOfOrderTen

/-- The cyclic group `C₁₀` itself has order 10. -/
theorem card_multiplicative_zmod_ten :
    Fintype.card (Multiplicative (ZMod 10)) = 10 := by
  rw [Fintype.card_multiplicative, ZMod.card]

/-- The dihedral group `D₅` itself has order 10. -/
theorem card_dihedralGroup_five : Fintype.card (DihedralGroup 5) = 10 := by
  rw [DihedralGroup.card]

/-- The classification places `C₁₀` in the cyclic case and not in the dihedral case. -/
theorem cyclic_case_of_zmod_ten :
    (Nonempty (Multiplicative (ZMod 10) ≃* Multiplicative (ZMod 10)) ∧
      ¬Nonempty (Multiplicative (ZMod 10) ≃* DihedralGroup 5)) := by
  have h := groups_of_order_10_classification_xor (Multiplicative (ZMod 10))
    card_multiplicative_zmod_ten
  rcases h with h | h
  · exact h
  · exfalso
    exact h.1 ⟨MulEquiv.refl _⟩

/-- The classification places `D₅` in the dihedral case and not in the cyclic case. -/
theorem dihedral_case_of_dihedralGroup_five :
    (¬Nonempty (DihedralGroup 5 ≃* Multiplicative (ZMod 10)) ∧
      Nonempty (DihedralGroup 5 ≃* DihedralGroup 5)) := by
  have h := groups_of_order_10_classification_xor (DihedralGroup 5) card_dihedralGroup_five
  rcases h with h | h
  · exfalso
    exact h.2 ⟨MulEquiv.refl _⟩
  · exact h

/-- `D₅` is not cyclic, so the helper theorem `mulEquiv_dihedralGroup_of_not_isCyclic`
applies to it directly. -/
theorem dihedralGroup_five_not_isCyclic : ¬IsCyclic (DihedralGroup 5) :=
  DihedralGroup.not_isCyclic (by norm_num : (5 : ℕ) ≠ 1)

example : Nonempty (DihedralGroup 5 ≃* DihedralGroup 5) :=
  mulEquiv_dihedralGroup_of_not_isCyclic (DihedralGroup 5) card_dihedralGroup_five
    dihedralGroup_five_not_isCyclic

/-- No group of order 10 is isomorphic to both `C₁₀` and `D₅`. -/
example (G : Type*) [Group G] [Fintype G] (_hG : Fintype.card G = 10) :
    ¬(Nonempty (G ≃* Multiplicative (ZMod 10)) ∧ Nonempty (G ≃* DihedralGroup 5)) := by
  rintro ⟨⟨e⟩, ⟨f⟩⟩
  have h : IsCyclic (DihedralGroup 5) := (f.symm.trans e).isCyclic.mpr inferInstance
  exact DihedralGroup.not_isCyclic (by norm_num : (5 : ℕ) ≠ 1) h

end MathlibExtTest.GroupTheory.GroupsOfOrderTen

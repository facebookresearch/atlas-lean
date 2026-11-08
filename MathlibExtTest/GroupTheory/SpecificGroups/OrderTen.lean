/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.SpecificGroups.OrderTen
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.NormNum

/-! Consumers of the shared dihedral constructor and the order-ten classification. -/
set_option autoImplicit false

namespace MetaMathlibExt

-- The order-two example: the cyclic subgroup has order two; the ambient group is D₂.
example : Nonempty (DihedralGroup 2 ≃* DihedralGroup 2) := by
  classical
  let H : Subgroup (DihedralGroup 2) := Subgroup.zpowers (DihedralGroup.r (1 : ZMod 2))
  have hHcard : Nat.card H = 2 := by
    change Nat.card (Subgroup.zpowers (DihedralGroup.r (1 : ZMod 2))) = 2
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  have hindex : H.index = 2 := by
    have h := H.card_mul_index
    rw [hHcard, DihedralGroup.nat_card] at h
    omega
  have houtside : ∀ g : DihedralGroup 2, g ∉ H → g ^ 2 = 1 := by
    intro g _
    cases g with
    | r i =>
        rw [DihedralGroup.r_pow]
        have hcast : (Nat.cast (2 : ℕ) : ZMod 2) = 0 := by decide
        rw [hcast, mul_zero, DihedralGroup.r_zero]
    | sr i => rw [sq, DihedralGroup.sr_mul_self]
  have h := nonempty_mulEquiv_dihedralGroup_of_index_eq_two H
    (inferInstance : IsCyclic H) hindex houtside
  rw [hHcard] at h
  exact h

-- Use the generic constructor at the actual order-ten dihedral group.
example : Nonempty (DihedralGroup 5 ≃* DihedralGroup 5) := by
  classical
  let H : Subgroup (DihedralGroup 5) := Subgroup.zpowers (DihedralGroup.r (1 : ZMod 5))
  have hHcard : Nat.card H = 5 := by
    change Nat.card (Subgroup.zpowers (DihedralGroup.r (1 : ZMod 5))) = 5
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  have hindex : H.index = 2 := by
    have h := H.card_mul_index
    rw [hHcard, DihedralGroup.nat_card] at h
    omega
  have houtside : ∀ g : DihedralGroup 5, g ∉ H → g ^ 2 = 1 := by
    intro g hg
    cases g with
    | r i =>
        exfalso
        apply hg
        change DihedralGroup.r i ∈ Subgroup.zpowers (DihedralGroup.r (1 : ZMod 5))
        have h := Subgroup.pow_mem (Subgroup.zpowers (DihedralGroup.r (1 : ZMod 5)))
          (Subgroup.mem_zpowers (DihedralGroup.r (1 : ZMod 5))) i.val
        simpa [DihedralGroup.r_pow] using h
    | sr i => rw [sq, DihedralGroup.sr_mul_self]
  have h := nonempty_mulEquiv_dihedralGroup_of_index_eq_two H
    (inferInstance : IsCyclic H) hindex houtside
  rw [hHcard] at h
  exact h

-- The noncyclic order-ten theorem has a concrete admissible instance.
example : Nonempty (DihedralGroup 5 ≃* DihedralGroup 5) :=
  nonempty_mulEquiv_dihedralGroup_of_card_eq_ten_of_not_isCyclic (DihedralGroup 5)
    (by simpa using (DihedralGroup.card (n := 5)))
    (DihedralGroup.not_isCyclic (by decide : (5 : ℕ) ≠ 1))

-- A separate caller checks the public boundary and the archived noncyclic theorem's binders.
example (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 10) (hnc : ¬IsCyclic G) :
    Nonempty (G ≃* DihedralGroup 5) :=
  nonempty_mulEquiv_dihedralGroup_of_card_eq_ten_of_not_isCyclic G hG hnc

-- The generic constructor also covers the boundary case of a trivial
-- rotation subgroup: `DihedralGroup 1` from `⊥` (and D₁ is cyclic).
example : Nonempty (DihedralGroup 1 ≃* DihedralGroup 1) := by
  have h := nonempty_mulEquiv_dihedralGroup_of_index_eq_two
    (⊥ : Subgroup (DihedralGroup 1)) inferInstance
    (by rw [Subgroup.index_bot, DihedralGroup.nat_card]) (by
      intro g _
      cases g with
      | r i =>
        fin_cases i
        decide
      | sr i =>
        fin_cases i
        decide)
  rwa [Nat.card_unique] at h

example : IsCyclic (DihedralGroup 1) := DihedralGroup.isCyclic_iff.mpr rfl

#print axioms nonempty_mulEquiv_dihedralGroup_of_index_eq_two
#print axioms nonempty_mulEquiv_dihedralGroup_of_card_eq_ten_of_not_isCyclic

end MetaMathlibExt

namespace MathlibExtTest.GroupTheory.GroupsOfOrderTen

open MetaMathlibExt

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

/-- `D₅` is not cyclic, so the helper theorem `MetaMathlibExt.nonempty_mulEquiv_dihedralGroup_of_card_eq_ten_of_not_isCyclic`
applies to it directly. -/
theorem dihedralGroup_five_not_isCyclic : ¬IsCyclic (DihedralGroup 5) :=
  DihedralGroup.not_isCyclic (by norm_num : (5 : ℕ) ≠ 1)

example : Nonempty (DihedralGroup 5 ≃* DihedralGroup 5) :=
  MetaMathlibExt.nonempty_mulEquiv_dihedralGroup_of_card_eq_ten_of_not_isCyclic (DihedralGroup 5) card_dihedralGroup_five
    dihedralGroup_five_not_isCyclic

/-- No group of order 10 is isomorphic to both `C₁₀` and `D₅`. -/
example (G : Type*) [Group G] [Fintype G] (_hG : Fintype.card G = 10) :
    ¬(Nonempty (G ≃* Multiplicative (ZMod 10)) ∧ Nonempty (G ≃* DihedralGroup 5)) := by
  rintro ⟨⟨e⟩, ⟨f⟩⟩
  have h : IsCyclic (DihedralGroup 5) := (f.symm.trans e).isCyclic.mpr inferInstance
  exact DihedralGroup.not_isCyclic (by norm_num : (5 : ℕ) ≠ 1) h

end MathlibExtTest.GroupTheory.GroupsOfOrderTen

namespace MetaMathlibExt

/-- The ordinary `C₁₀` classification has the archived Lean statement's signature. -/
example (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 10) :
    Nonempty (G ≃* Multiplicative (ZMod 10)) ∨ Nonempty (G ≃* DihedralGroup 5) :=
  groups_of_order_10_classification G hG

/-- The exclusive classification retains both alternatives. -/
example (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 10) :
    (Nonempty (G ≃* Multiplicative (ZMod 10)) ∧ ¬Nonempty (G ≃* DihedralGroup 5)) ∨
      (¬Nonempty (G ≃* Multiplicative (ZMod 10)) ∧ Nonempty (G ≃* DihedralGroup 5)) :=
  groups_of_order_10_classification_xor G hG

#print axioms groups_of_order_10_classification
#print axioms groups_of_order_10_classification_xor

end MetaMathlibExt

namespace ProductClassificationPublicClient

private abbrev CyclicProduct := Multiplicative (ZMod 5) × Multiplicative (ZMod 2)

private theorem card_cyclicProduct : Fintype.card CyclicProduct = 10 := by
  norm_num [CyclicProduct, Fintype.card_prod, Fintype.card_multiplicative, ZMod.card]

private theorem cyclicProduct_isCyclic : IsCyclic CyclicProduct := by
  apply Group.isCyclic_prod_iff.mpr
  refine ⟨inferInstance, inferInstance, ?_⟩
  simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    using (by decide : Nat.Coprime 5 2)

private theorem cyclicProduct_not_dihedral : ¬Nonempty (CyclicProduct ≃* DihedralGroup 5) := by
  rintro ⟨e⟩
  exact DihedralGroup.not_isCyclic (by decide : (5 : ℕ) ≠ 1)
    (e.symm.isCyclic.mpr cyclicProduct_isCyclic)

/-- The public corollary has the literal cyclic-product target recorded in AlgebraNotes. -/
example (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 10) :
    Nonempty (G ≃* (Multiplicative (ZMod 5) × Multiplicative (ZMod 2))) ∨
      Nonempty (G ≃* DihedralGroup 5) :=
  MetaMathlibExt.groups_of_order_10_classification_prod G hG

/-- The actual product group occupies the product branch and excludes the dihedral branch. -/
example : Nonempty (CyclicProduct ≃* CyclicProduct) ∧
    ¬Nonempty (CyclicProduct ≃* DihedralGroup 5) := by
  have h : Nonempty (CyclicProduct ≃* CyclicProduct) ∨
      Nonempty (CyclicProduct ≃* DihedralGroup 5) :=
    MetaMathlibExt.groups_of_order_10_classification_prod CyclicProduct card_cyclicProduct
  exact ⟨h.resolve_right cyclicProduct_not_dihedral, cyclicProduct_not_dihedral⟩

/-- The actual dihedral group occupies the dihedral branch and excludes the product branch. -/
example : ¬Nonempty (DihedralGroup 5 ≃* CyclicProduct) ∧
    Nonempty (DihedralGroup 5 ≃* DihedralGroup 5) := by
  have hnot : ¬Nonempty (DihedralGroup 5 ≃* CyclicProduct) := by
    rintro ⟨e⟩
    exact DihedralGroup.not_isCyclic (by decide : (5 : ℕ) ≠ 1)
      (e.isCyclic.mpr cyclicProduct_isCyclic)
  have h : Nonempty (DihedralGroup 5 ≃* CyclicProduct) ∨
      Nonempty (DihedralGroup 5 ≃* DihedralGroup 5) :=
    MetaMathlibExt.groups_of_order_10_classification_prod (DihedralGroup 5)
      (by simpa using (DihedralGroup.card (n := 5)))
  exact ⟨hnot, h.resolve_left hnot⟩

/-- The two recorded models cannot both describe one group. -/
example (G : Type*) [Group G] :
    ¬(Nonempty (G ≃* CyclicProduct) ∧ Nonempty (G ≃* DihedralGroup 5)) := by
  rintro ⟨⟨e⟩, ⟨f⟩⟩
  exact DihedralGroup.not_isCyclic (by decide : (5 : ℕ) ≠ 1)
    ((f.symm.trans e).isCyclic.mpr cyclicProduct_isCyclic)

end ProductClassificationPublicClient

namespace ProductXorPublicClient

private abbrev CyclicProduct := Multiplicative (ZMod 5) × Multiplicative (ZMod 2)

/-- The public exclusive statement uses the two literal recorded models. -/
example (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 10) :
    (Nonempty (G ≃* (Multiplicative (ZMod 5) × Multiplicative (ZMod 2))) ∧
      ¬Nonempty (G ≃* DihedralGroup 5)) ∨
    (¬Nonempty (G ≃* (Multiplicative (ZMod 5) × Multiplicative (ZMod 2))) ∧
      Nonempty (G ≃* DihedralGroup 5)) :=
  MetaMathlibExt.groups_of_order_10_classification_prod_xor G hG

/-- The exclusive API selects the product case on the actual cyclic product. -/
example : Nonempty (CyclicProduct ≃* CyclicProduct) ∧
    ¬Nonempty (CyclicProduct ≃* DihedralGroup 5) := by
  have h : (Nonempty (CyclicProduct ≃* CyclicProduct) ∧
      ¬Nonempty (CyclicProduct ≃* DihedralGroup 5)) ∨
    (¬Nonempty (CyclicProduct ≃* CyclicProduct) ∧
      Nonempty (CyclicProduct ≃* DihedralGroup 5)) :=
    MetaMathlibExt.groups_of_order_10_classification_prod_xor CyclicProduct
      (by norm_num [CyclicProduct, Fintype.card_prod, Fintype.card_multiplicative, ZMod.card])
  rcases h with h | h
  · exact h
  · exact False.elim (h.1 ⟨MulEquiv.refl _⟩)

/-- The exclusive API selects the dihedral case on the actual dihedral group. -/
example : ¬Nonempty (DihedralGroup 5 ≃* CyclicProduct) ∧
    Nonempty (DihedralGroup 5 ≃* DihedralGroup 5) := by
  have h : (Nonempty (DihedralGroup 5 ≃* CyclicProduct) ∧
      ¬Nonempty (DihedralGroup 5 ≃* DihedralGroup 5)) ∨
    (¬Nonempty (DihedralGroup 5 ≃* CyclicProduct) ∧
      Nonempty (DihedralGroup 5 ≃* DihedralGroup 5)) :=
    MetaMathlibExt.groups_of_order_10_classification_prod_xor (DihedralGroup 5)
      (by simpa using (DihedralGroup.card (n := 5)))
  rcases h with h | h
  · exact False.elim (h.2 ⟨MulEquiv.refl _⟩)
  · exact h

end ProductXorPublicClient

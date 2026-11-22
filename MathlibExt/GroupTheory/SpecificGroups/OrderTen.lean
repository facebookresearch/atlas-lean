/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.SpecificGroups.Dihedral.IndexTwo
public import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Groups of order ten

Adapted from `v1/Atlas/AlgebraNotes/code/SylowTheorems.lean`, lines 108-325 at
commit `8de8f74fa5760eb8b768a9804494ca2ab631cf87`.
The `C₁₀` corollaries preserve the archived Lean classification's domains and
hypotheses. The recorded target in `v1/Atlas/AlgebraNotes/targets.yaml`, lines
297-301, instead writes the cyclic alternative as `C₅ × C₂`.
`groups_of_order_10_classification_prod` gives those alternatives, and
`groups_of_order_10_classification_prod_xor` states that exactly one holds.
This provenance compares archived code and its recorded target with this file;
the unavailable textbook PDF has not been verified.

All classification corollaries reuse the canonical noncyclic theorem.
The product corollary constructs `C₁₀ ≃* C₅ × C₂` with Mathlib's Chinese
remainder equivalence and the multiplicative type-tag product equivalence.
The `C₁₀` and `D₅` alternatives are exclusive, as recorded by
`groups_of_order_10_classification_xor`.
-/
set_option autoImplicit false

namespace MetaMathlibExt
@[expose] public section
open Finset Nat MulAction Subgroup

private lemma conjugation_pow_four
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 10) (hnc : ¬IsCyclic G)
    (x y : G) (hx5 : orderOf x = 5) (hy2 : orderOf y = 2) :
    y * x * y⁻¹ = x ^ 4 := by
  classical
  have hy_sq : y * y = 1 := by
    simpa [sq] using (show y ^ 2 = 1 from by rw [← hy2]; exact pow_orderOf_eq_one y)
  have hy_inv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy_sq
  have hindex : (Subgroup.zpowers x).index = 2 := by
    have h := (Subgroup.zpowers x).card_mul_index
    rw [Nat.card_zpowers, hx5, Nat.card_eq_fintype_card, hG] at h
    omega
  have hN : (Subgroup.zpowers x).Normal := Subgroup.normal_of_index_eq_two hindex
  have hconj_mem : y * x * y⁻¹ ∈ Subgroup.zpowers x :=
    hN.conj_mem x (Subgroup.mem_zpowers x) y
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hconj_mem

  have hkk : x ^ (k * k) = x := by
    have hphi : y * x ^ k * y⁻¹ = (y * x * y⁻¹) ^ k := conj_zpow.symm
    rw [hk.symm, ← zpow_mul] at hphi

    have hphi2 : y * (y * x * y⁻¹) * y⁻¹ = x := by
      rw [hy_inv]
      calc y * (y * x * y) * y = (y * y) * x * (y * y) := by group
        _ = x := by rw [hy_sq, one_mul, mul_one]

    rw [hk] at hphi

    rw [hphi2] at hphi

    exact hphi.symm

  have h5dvd : (5 : ℤ) ∣ k * k - 1 := by
    have h1 : x ^ (k * k - 1) = 1 := by
      have : x ^ (k * k) * x⁻¹ = 1 := by rw [hkk, mul_inv_cancel]
      rwa [← zpow_neg_one, ← zpow_add] at this
    have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hx5] at h2; exact_mod_cast h2
  have hk_mod : k % 5 = 1 ∨ k % 5 = 4 := by
    have hmod5 : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
    have hkey : (k % 5) * (k % 5) % 5 = 1 := by
      have h3 : (k * k) % 5 = 1 := by omega
      have h4 : (k * k) % 5 = (k % 5 * (k % 5)) % 5 := Int.mul_emod k k 5
      omega
    rcases hmod5 with h | h | h | h | h <;> simp_all
  rcases hk_mod with hk1 | hk4
  ·
    exfalso; apply hnc
    have hyx_eq_x : y * x * y⁻¹ = x := by
      rw [← hk]; conv_lhs => rw [← zpow_mod_orderOf x k]
      rw [hx5]; simp only [Nat.cast_ofNat]
      rw [show k % (5 : ℤ) = 1 from hk1]; simp
    have hcomm : Commute x y := by
      have h : x * y = y * x := by
        have h1 : y * x * y⁻¹ = x := hyx_eq_x
        have h2 : y * x = x * y := by
          calc y * x = y * x * y⁻¹ * y := by rw [inv_mul_cancel_right]
            _ = x * y := by rw [h1]
        exact h2.symm
      exact h
    have hord : orderOf (x * y) = 10 := by
      have := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx5, hy2]; norm_num)
      rw [hx5, hy2] at this; exact this
    exact isCyclic_of_orderOf_eq_card (x * y) (by rw [hord, Nat.card_eq_fintype_card, hG])
  ·
    rw [← hk]; conv_lhs => rw [← zpow_mod_orderOf x k]
    rw [hx5]; simp only [Nat.cast_ofNat]
    rw [show k % (5 : ℤ) = 4 from hk4]
    norm_num

private lemma outside_square_one
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 10) (hnc : ¬IsCyclic G)
    (x y : G) (hx5 : orderOf x = 5) (hy2 : orderOf y = 2) :
    ∀ g : G, g ∉ Subgroup.zpowers x → g ^ 2 = 1 := by
  classical
  have hy_sq : y * y = 1 := by
    simpa [sq] using (show y ^ 2 = 1 from by rw [← hy2]; exact pow_orderOf_eq_one y)
  have hy_inv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy_sq
  have hindex : (Subgroup.zpowers x).index = 2 := by
    have h := (Subgroup.zpowers x).card_mul_index
    rw [Nat.card_zpowers, hx5, Nat.card_eq_fintype_card, hG] at h
    omega
  have hy_not : y ∉ Subgroup.zpowers x := by
    intro hy
    have h := Subgroup.orderOf_dvd_natCard _ hy
    rw [Nat.card_zpowers, hx5, hy2] at h
    omega
  have hx5one : x ^ 5 = 1 := by
    rw [← hx5]
    exact pow_orderOf_eq_one x
  have hfour : x ^ 4 = x⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc x ^ 4 * x = x ^ 5 := (pow_succ x 4).symm
         _ = 1 := hx5one
  have hconj_inverse : y * x * y⁻¹ = x⁻¹ :=
    (conjugation_pow_four G hG hnc x y hx5 hy2).trans hfour
  intro g hg
  have hmul : y⁻¹ * g ∈ Subgroup.zpowers x := by
    rw [Subgroup.mul_mem_iff_of_index_two hindex]
    simp [hy_not, hg]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmul
  have hdecomp : g = y * x ^ k := by
    rw [hk]
    group
  have hconjk : y * x ^ k * y⁻¹ = (x ^ k)⁻¹ := by
    calc y * x ^ k * y⁻¹ = (y * x * y⁻¹) ^ k := conj_zpow.symm
         _ = (x⁻¹) ^ k := by rw [hconj_inverse]
         _ = (x ^ k)⁻¹ := by simp
  rw [hdecomp, sq]
  calc (y * x ^ k) * (y * x ^ k) = (y * x ^ k * y⁻¹) * x ^ k := by
         rw [hy_inv]
         group
       _ = (x ^ k)⁻¹ * x ^ k := by rw [hconjk]
       _ = 1 := inv_mul_cancel _

/-- Every noncyclic group of cardinality ten is isomorphic to the dihedral group of
order ten. The generators and inversion argument are adapted from the archived
AlgebraNotes source; the final isomorphism uses the shared index-two constructor. -/
theorem nonempty_mulEquiv_dihedralGroup_of_card_eq_ten_of_not_isCyclic
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 10) (hnc : ¬IsCyclic G) :
    Nonempty (G ≃* DihedralGroup 5) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨x, hx5⟩ := exists_prime_orderOf_dvd_card 5 (by omega : (5 : ℕ) ∣ Fintype.card G)
  obtain ⟨y, hy2⟩ := exists_prime_orderOf_dvd_card 2 (by omega : (2 : ℕ) ∣ Fintype.card G)
  have hindex : (Subgroup.zpowers x).index = 2 := by
    have h := (Subgroup.zpowers x).card_mul_index
    rw [Nat.card_zpowers, hx5, Nat.card_eq_fintype_card, hG] at h
    omega
  have houtside : ∀ g : G, g ∉ Subgroup.zpowers x → g ^ 2 = 1 :=
    outside_square_one G hG hnc x y hx5 hy2
  have h := nonempty_mulEquiv_dihedralGroup_of_index_eq_two
    (Subgroup.zpowers x) (inferInstance : IsCyclic (Subgroup.zpowers x)) hindex houtside
  have hcard : Nat.card (Subgroup.zpowers x) = 5 := by
    rw [Nat.card_zpowers, hx5]
  rw [hcard] at h
  exact h

/-- **Classification of groups of order 10.** Every group of order 10 is
isomorphic either to the cyclic group `C₁₀` (as `Multiplicative (ZMod 10)`)
or to the dihedral group `D₅` (`DihedralGroup 5`). See
`groups_of_order_10_classification_xor` for the exclusive form: exactly one
of the two alternatives holds. -/
theorem groups_of_order_10_classification
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 10) :
    Nonempty (G ≃* Multiplicative (ZMod 10)) ∨ Nonempty (G ≃* DihedralGroup 5) := by
  by_cases hcyc : IsCyclic G
  · left
    have hcard : Nat.card G = 10 := by rwa [Nat.card_eq_fintype_card]
    have e := zmodCyclicMulEquiv hcyc
    rw [hcard] at e
    exact ⟨e.symm⟩
  · right
    exact MetaMathlibExt.nonempty_mulEquiv_dihedralGroup_of_card_eq_ten_of_not_isCyclic G hG hcyc

/-- **Exclusive classification of groups of order 10.** Exactly one of the two
alternatives in `groups_of_order_10_classification` holds: a group of order 10
cannot be isomorphic to both `C₁₀` and `D₅`, since `C₁₀` is cyclic while
`DihedralGroup 5` is not (`DihedralGroup.not_isCyclic`), and cyclicity is
preserved under multiplicative equivalences. -/
theorem groups_of_order_10_classification_xor
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 10) :
    (Nonempty (G ≃* Multiplicative (ZMod 10)) ∧ ¬Nonempty (G ≃* DihedralGroup 5)) ∨
      (¬Nonempty (G ≃* Multiplicative (ZMod 10)) ∧ Nonempty (G ≃* DihedralGroup 5)) := by
  have hnotboth : ¬(Nonempty (G ≃* Multiplicative (ZMod 10)) ∧
      Nonempty (G ≃* DihedralGroup 5)) := by
    rintro ⟨⟨e⟩, ⟨f⟩⟩
    have h : IsCyclic (DihedralGroup 5) :=
      (f.symm.trans e).isCyclic.mpr inferInstance
    exact DihedralGroup.not_isCyclic (by norm_num : (5 : ℕ) ≠ 1) h
  rcases groups_of_order_10_classification G hG with ⟨⟨e⟩⟩ | ⟨⟨f⟩⟩
  · exact Or.inl ⟨⟨e⟩, fun h => hnotboth ⟨⟨e⟩, h⟩⟩
  · exact Or.inr ⟨fun h => hnotboth ⟨h, ⟨f⟩⟩, ⟨f⟩⟩

/-- **Classification in the recorded product form.** Every group of order ten
is isomorphic to `C₅ × C₂` or `D₅`, as stated in
`v1/Atlas/AlgebraNotes/targets.yaml`, lines 297-301. The cyclic branch is
transported from `C₁₀` by Mathlib's Chinese remainder equivalence. See
`groups_of_order_10_classification_prod_xor` for the exclusive form. -/
theorem groups_of_order_10_classification_prod
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 10) :
    Nonempty (G ≃* (Multiplicative (ZMod 5) × Multiplicative (ZMod 2))) ∨
      Nonempty (G ≃* DihedralGroup 5) := by
  let eProd : Multiplicative (ZMod 10) ≃*
      (Multiplicative (ZMod 5) × Multiplicative (ZMod 2)) :=
    (ZMod.chineseRemainder (by decide : Nat.Coprime 5 2)).toAddEquiv.toMultiplicative.trans
      (MulEquiv.prodMultiplicative (ZMod 5) (ZMod 2))
  rcases groups_of_order_10_classification G hG with hC | hD
  · rcases hC with ⟨e⟩
    exact Or.inl ⟨e.trans eProd⟩
  · exact Or.inr hD

/-- **Exclusive classification in the recorded product form.** Exactly one of
the `C₅ × C₂` and `D₅` alternatives holds for a group of order ten, as in
`v1/Atlas/AlgebraNotes/targets.yaml`, lines 297-301. The product is cyclic
and `D₅` is not, so the ordinary product classification is exclusive. -/
theorem groups_of_order_10_classification_prod_xor
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 10) :
    (Nonempty (G ≃* (Multiplicative (ZMod 5) × Multiplicative (ZMod 2))) ∧
      ¬Nonempty (G ≃* DihedralGroup 5)) ∨
    (¬Nonempty (G ≃* (Multiplicative (ZMod 5) × Multiplicative (ZMod 2))) ∧
      Nonempty (G ≃* DihedralGroup 5)) := by
  have hcyc : IsCyclic (Multiplicative (ZMod 5) × Multiplicative (ZMod 2)) := by
    apply Group.isCyclic_prod_iff.mpr
    refine ⟨inferInstance, inferInstance, ?_⟩
    simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
      using (by decide : Nat.Coprime 5 2)
  have hnotboth : ¬(Nonempty (G ≃* (Multiplicative (ZMod 5) × Multiplicative (ZMod 2))) ∧
      Nonempty (G ≃* DihedralGroup 5)) := by
    rintro ⟨⟨e⟩, ⟨f⟩⟩
    exact DihedralGroup.not_isCyclic (by decide : (5 : ℕ) ≠ 1)
      ((f.symm.trans e).isCyclic.mpr hcyc)
  rcases groups_of_order_10_classification_prod G hG with hP | hD
  · exact Or.inl ⟨hP, fun hD => hnotboth ⟨hP, hD⟩⟩
  · exact Or.inr ⟨fun hP => hnotboth ⟨hP, hD⟩, hD⟩

end

end MetaMathlibExt

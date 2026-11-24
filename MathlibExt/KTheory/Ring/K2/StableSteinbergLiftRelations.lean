/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.StableSteinbergCentralLift
public import Mathlib.GroupTheory.Commutator.Basic

/-! # Lifted Steinberg relations

Lifted additive, distant-commutation, and Chevalley relations for
`centralLiftGenerator` in a central extension of `StableE R`.
-/

@[expose] public section

namespace AlgebraicKTheory

namespace StableSteinberg

universe u v w

variable {R : Type u} [Ring R] {N : Type v} {E : Type w} [Group N] [Group E]

open scoped commutatorElement

-- Central triple lemma: if q(a) and q(b) each commute with q(c) then [[a,b],c]=1
private theorem centralTriple_commutator_eq_one
    {G : Type*} [Group G] {S : GroupExtension N E G} (hS : S.IsCentral)
    (a b c : E)
    (h_ac : Commute (S.rightHom a) (S.rightHom c))
    (h_bc : Commute (S.rightHom b) (S.rightHom c)) :
    ⁅⁅a, b⁆, c⁆ = 1 := by
  have h_ac_eq : S.rightHom a * S.rightHom c = S.rightHom c * S.rightHom a := h_ac.eq
  have h_bc_eq : S.rightHom b * S.rightHom c = S.rightHom c * S.rightHom b := h_bc.eq
  have h_q_cac : S.rightHom (c * a * c⁻¹) = S.rightHom a := by
    simp only [map_mul, map_inv]
    calc S.rightHom c * S.rightHom a * (S.rightHom c)⁻¹
        = S.rightHom a * S.rightHom c * (S.rightHom c)⁻¹ := by rw [← h_ac_eq]
      _ = S.rightHom a * (S.rightHom c * (S.rightHom c)⁻¹) := by rw [mul_assoc]
      _ = S.rightHom a * 1 := by rw [mul_inv_cancel]
      _ = S.rightHom a := by rw [mul_one]
  have h_q_cbc : S.rightHom (c * b * c⁻¹) = S.rightHom b := by
    simp only [map_mul, map_inv]
    calc S.rightHom c * S.rightHom b * (S.rightHom c)⁻¹
        = S.rightHom b * S.rightHom c * (S.rightHom c)⁻¹ := by rw [← h_bc_eq]
      _ = S.rightHom b * (S.rightHom c * (S.rightHom c)⁻¹) := by rw [mul_assoc]
      _ = S.rightHom b * 1 := by rw [mul_inv_cancel]
      _ = S.rightHom b := by rw [mul_one]
  have h_conj : c * ⁅a, b⁆ * c⁻¹ = ⁅c * a * c⁻¹, c * b * c⁻¹⁆ := by
    rw [conjugate_commutatorElement]
  have h_comm_eq : ⁅c * a * c⁻¹, c * b * c⁻¹⁆ = ⁅a, b⁆ := by
    apply hS.commutator_eq_of_rightHom_eq
    · exact h_q_cac
    · exact h_q_cbc
  have h_conj_eq : c * ⁅a, b⁆ * c⁻¹ = ⁅a, b⁆ := by
    rw [h_conj, h_comm_eq]
  have h_eq : c * ⁅a, b⁆ = ⁅a, b⁆ * c := by
    calc c * ⁅a, b⁆ = c * ⁅a, b⁆ * c⁻¹ * c := by rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = ⁅a, b⁆ * c := by rw [h_conj_eq]
  have h_comm : Commute ⁅a, b⁆ c := by
    rw [Commute]
    exact h_eq.symm
  exact h_comm.commutator_eq

-- Arbitrary lifts of distant stable elementary roots commute exactly
private theorem distant_lift_comm
    {S : GroupExtension N E (StableE R)} (hS : S.IsCentral)
    (i j k l : ℕ) (hij : i ≠ j) (hkl : k ≠ l) (hil : i ≠ l) (hjk : j ≠ k)
    (a b : R) (u v : E)
    (hu : S.rightHom u = StableE.natElementary i j hij a)
    (hv : S.rightHom v = StableE.natElementary k l hkl b) :
    ⁅u, v⁆ = 1 := by
  let t := max (max i j) (max k l) + 1
  have hi_lt : i < t := by
    have h1 : i ≤ max i j := Nat.le_max_left i j
    have h2 : max i j ≤ max (max i j) (max k l) := Nat.le_max_left _ _
    omega
  have hj_lt : j < t := by
    have h1 : j ≤ max i j := Nat.le_max_right i j
    have h2 : max i j ≤ max (max i j) (max k l) := Nat.le_max_left _ _
    omega
  have hk_lt : k < t := by
    have h1 : k ≤ max k l := Nat.le_max_left k l
    have h2 : max k l ≤ max (max i j) (max k l) := Nat.le_max_right _ _
    omega
  have hl_lt : l < t := by
    have h1 : l ≤ max k l := Nat.le_max_right k l
    have h2 : max k l ≤ max (max i j) (max k l) := Nat.le_max_right _ _
    omega
  have h_it : i ≠ t := Nat.ne_of_lt hi_lt
  have h_tj : t ≠ j := Nat.ne_of_gt hj_lt
  have h_tk : t ≠ k := Nat.ne_of_gt hk_lt
  have h_tl : t ≠ l := Nat.ne_of_gt hl_lt
  let a1 : StableE R := StableE.natElementary i t h_it a
  let b1 : StableE R := StableE.natElementary t j h_tj (1 : R)
  have h_chev : ⁅a1, b1⁆ = StableE.natElementary i j hij a := by
    have h := StableE.natElementary_chev i t j h_it h_tj hij a (1 : R)
    simpa [a1, b1, mul_one] using h
  let A : E := S.surjInvRightHom a1
  let B : E := S.surjInvRightHom b1
  have hA : S.rightHom A = a1 := S.surjInvRightHom.rightInverse_rightHom a1
  have hB : S.rightHom B = b1 := S.surjInvRightHom.rightInverse_rightHom b1
  have hAB : S.rightHom ⁅A, B⁆ = StableE.natElementary i j hij a := by
    have h_map : S.rightHom ⁅A, B⁆ = ⁅S.rightHom A, S.rightHom B⁆ :=
      map_commutatorElement S.rightHom A B
    rw [h_map, hA, hB, h_chev]
  have h_eq : ⁅u, v⁆ = ⁅⁅A, B⁆, v⁆ := by
    apply hS.commutator_eq_of_rightHom_eq
    · rw [hAB, hu]
    · rfl
  rw [h_eq]
  have h_comm_Av : Commute (S.rightHom A) (S.rightHom v) := by
    rw [hA, hv]
    have h1 : i ≠ l := hil
    have h2 : t ≠ k := h_tk
    have hcomm : ⁅StableE.natElementary i t h_it a, StableE.natElementary k l hkl b⁆ = 1 :=
      StableE.natElementary_comm i t k l h_it hkl h1 h2 a b
    exact (commutatorElement_eq_one_iff_commute.mp hcomm)
  have h_comm_Bv : Commute (S.rightHom B) (S.rightHom v) := by
    rw [hB, hv]
    have h1 : t ≠ l := h_tl
    have h2 : j ≠ k := hjk
    have hcomm : ⁅StableE.natElementary t j h_tj (1 : R), StableE.natElementary k l hkl b⁆ = 1 :=
      StableE.natElementary_comm t j k l h_tj hkl h1 h2 (1 : R) b
    exact (commutatorElement_eq_one_iff_commute.mp hcomm)
  exact centralTriple_commutator_eq_one hS A B v h_comm_Av h_comm_Bv

-- Hall-Witt bridge [[a,b],c]=[a,[b,c]] under three exact commutations
private theorem hallWittBridge
    {G : Type*} [Group G] (a b c : G)
    (hac : ⁅a, c⁆ = 1)
    (hab_bc : ⁅⁅a, b⁆, ⁅b, c⁆⁆ = 1)
    (habc_bc : ⁅⁅⁅a, b⁆, c⁆, ⁅b, c⁆⁆ = 1) :
    ⁅⁅a, b⁆, c⁆ = ⁅a, ⁅b, c⁆⁆ := by
  have hall := commutatorElement_commutatorElement_conj_mul a b c
  have hca : ⁅c, a⁆ = 1 := by
    have h : ⁅a, c⁆⁻¹ = ⁅c, a⁆ := commutatorElement_inv a c
    rw [hac, inv_one] at h
    exact h.symm
  have h_third : ⁅⁅c, a⁆, a * b * a⁻¹⁆ = 1 := by
    rw [hca, commutatorElement_one_left]
  have h_ac_comm : Commute a c := commutatorElement_eq_one_iff_commute.mp hac
  have h_ac_eq : a * c = c * a := h_ac_comm.eq
  have h_cac : c * a * c⁻¹ = a := by
    calc c * a * c⁻¹ = a * c * c⁻¹ := by rw [← h_ac_eq]
      _ = a * (c * c⁻¹) := by rw [mul_assoc]
      _ = a * 1 := by rw [mul_inv_cancel]
      _ = a := by rw [mul_one]
  have hY : ⁅⁅b, c⁆, c * a * c⁻¹⁆ = ⁅⁅b, c⁆, a⁆ := by rw [h_cac]
  have h_hall_simp : ⁅⁅a, b⁆, b * c * b⁻¹⁆ * ⁅⁅b, c⁆, a⁆ = 1 := by
    have h_eq : ⁅⁅a, b⁆, b * c * b⁻¹⁆ * ⁅⁅b, c⁆, c * a * c⁻¹⁆ * ⁅⁅c, a⁆, a * b * a⁻¹⁆
        = ⁅⁅a, b⁆, b * c * b⁻¹⁆ * ⁅⁅b, c⁆, a⁆ := by
      rw [hY, h_third, mul_one]
    rw [h_eq] at hall
    exact hall
  have h_X_eq : ⁅⁅a, b⁆, b * c * b⁻¹⁆ = ⁅a, ⁅b, c⁆⁆ := by
    have h_mul : ⁅⁅a, b⁆, b * c * b⁻¹⁆ * ⁅⁅b, c⁆, a⁆ = 1 := h_hall_simp
    have h_inv : ⁅⁅a, b⁆, b * c * b⁻¹⁆ = (⁅⁅b, c⁆, a⁆)⁻¹ :=
      eq_inv_of_mul_eq_one_left h_mul
    have h_inv2 : (⁅⁅b, c⁆, a⁆)⁻¹ = ⁅a, ⁅b, c⁆⁆ := by
      rw [commutatorElement_inv]
    rw [h_inv, h_inv2]
  have h_bcb : b * c * b⁻¹ = ⁅b, c⁆ * c := by
    have h : ⁅b, c⁆ * c = b * c * b⁻¹ := by
      simp only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one]
    exact h.symm
  rw [h_bcb] at h_X_eq
  have h_expand : ⁅⁅a, b⁆, ⁅b, c⁆ * c⁆ =
      ⁅⁅a, b⁆, ⁅b, c⁆⁆ * ⁅b, c⁆ * ⁅⁅a, b⁆, c⁆ * (⁅b, c⁆)⁻¹ := by
    have h := commutatorElement_mul_right_eq_mul_conj ⁅a, b⁆ ⁅b, c⁆ c
    exact h
  rw [h_expand] at h_X_eq
  have h_one : ⁅⁅a, b⁆, ⁅b, c⁆⁆ = 1 := hab_bc
  rw [h_one, one_mul] at h_X_eq
  have h_comm : Commute ⁅⁅a, b⁆, c⁆ ⁅b, c⁆ :=
    commutatorElement_eq_one_iff_commute.mp habc_bc
  have h_conj : ⁅b, c⁆ * ⁅⁅a, b⁆, c⁆ * (⁅b, c⁆)⁻¹ = ⁅⁅a, b⁆, c⁆ := by
    have h_eq : ⁅b, c⁆ * ⁅⁅a, b⁆, c⁆ = ⁅⁅a, b⁆, c⁆ * ⁅b, c⁆ := h_comm.eq.symm
    calc ⁅b, c⁆ * ⁅⁅a, b⁆, c⁆ * (⁅b, c⁆)⁻¹
        = ⁅⁅a, b⁆, c⁆ * ⁅b, c⁆ * (⁅b, c⁆)⁻¹ := by rw [h_eq]
      _ = ⁅⁅a, b⁆, c⁆ * (⁅b, c⁆ * (⁅b, c⁆)⁻¹) := by rw [mul_assoc]
      _ = ⁅⁅a, b⁆, c⁆ * 1 := by rw [mul_inv_cancel]
      _ = ⁅⁅a, b⁆, c⁆ := by rw [mul_one]
  rw [h_conj] at h_X_eq
  exact h_X_eq

/-- Auxiliary-index independence for the canonical central lift.

For a central extension `S : GroupExtension N E (StableE R)` over an arbitrary
ring `R`, the canonical generator `centralLiftGenerator S ⟨i, j, hij, a⟩`
(defined via the fresh index `max i j + 1`) coincides with `⁅u, v⁆` for *any*
auxiliary index `k` distinct from `i` and `j` and any lifts `u, v : E` with
`S.rightHom u = StableE.natElementary i k _ a` and
`S.rightHom v = StableE.natElementary k j _ 1`. The proof uses only centrality
of `S` and the Hall–Witt identity (via exact distant-commutation), not a
chosen set-theoretic splitting of `S`. -/
theorem centralLiftGenerator_eq_commutator_of_aux
    {S : GroupExtension N E (StableE R)} (hS : S.IsCentral)
    (i j k : ℕ) (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) (a : R)
    (u v : E)
    (hu : S.rightHom u = StableE.natElementary i k hik a)
    (hv : S.rightHom v = StableE.natElementary k j hkj (1 : R)) :
    centralLiftGenerator (R := R) (N := N) (E := E) S ⟨i, j, hij, a⟩ = ⁅u, v⁆ := by
  let m := max i j + 1
  have hm_gt_i : i < m := by
    have : i ≤ max i j := Nat.le_max_left i j
    omega
  have hm_gt_j : j < m := by
    have : j ≤ max i j := Nat.le_max_right i j
    omega
  have h_im : i ≠ m := Nat.ne_of_lt hm_gt_i
  have h_mj : m ≠ j := Nat.ne_of_gt hm_gt_j
  by_cases hkm : k = m
  · subst hkm
    have hu' : S.rightHom u = StableE.natElementary i m h_im a := hu
    have hv' : S.rightHom v = StableE.natElementary m j h_mj (1 : R) := hv
    exact centralLiftGenerator_eq_commutator hS i j hij a u v hu' hv'
  · have h_km : k ≠ m := hkm
    have h_mk : m ≠ k := Ne.symm h_km
    have h_ik : i ≠ k := hik
    let A : E := S.surjInvRightHom (StableE.natElementary i m h_im a)
    let B : E := S.surjInvRightHom (StableE.natElementary m k h_mk (1 : R))
    let C : E := S.surjInvRightHom (StableE.natElementary k j hkj (1 : R))
    have hA : S.rightHom A = StableE.natElementary i m h_im a :=
      S.surjInvRightHom.rightInverse_rightHom (StableE.natElementary i m h_im a)
    have hB : S.rightHom B = StableE.natElementary m k h_mk (1 : R) :=
      S.surjInvRightHom.rightInverse_rightHom (StableE.natElementary m k h_mk (1 : R))
    have hC : S.rightHom C = StableE.natElementary k j hkj (1 : R) :=
      S.surjInvRightHom.rightInverse_rightHom (StableE.natElementary k j hkj (1 : R))
    have h_ik_chev : ⁅StableE.natElementary i m h_im a, StableE.natElementary m k h_mk (1 : R)⁆
        = StableE.natElementary i k hik a := by
      have h := StableE.natElementary_chev i m k h_im h_mk h_ik a (1 : R)
      simpa [mul_one] using h
    have h_mj_chev : ⁅StableE.natElementary m k h_mk (1 : R), StableE.natElementary k j hkj (1 : R)⁆
        = StableE.natElementary m j h_mj (1 : R) := by
      have h := StableE.natElementary_chev m k j h_mk hkj h_mj (1 : R) (1 : R)
      simpa [mul_one] using h
    have hAB : S.rightHom ⁅A, B⁆ = StableE.natElementary i k hik a := by
      have h_map : S.rightHom ⁅A, B⁆ = ⁅S.rightHom A, S.rightHom B⁆ :=
        map_commutatorElement S.rightHom A B
      rw [h_map, hA, hB, h_ik_chev]
    have hBC : S.rightHom ⁅B, C⁆ = StableE.natElementary m j h_mj (1 : R) := by
      have h_map : S.rightHom ⁅B, C⁆ = ⁅S.rightHom B, S.rightHom C⁆ :=
        map_commutatorElement S.rightHom B C
      rw [h_map, hB, hC, h_mj_chev]
    have h_arbitrary : ⁅u, v⁆ = ⁅⁅A, B⁆, C⁆ := by
      apply hS.commutator_eq_of_rightHom_eq
      · rw [hAB, hu]
      · rw [hC, hv]
    have h_canonical : centralLiftGenerator (R := R) (N := N) (E := E) S ⟨i, j, hij, a⟩ =
        ⁅A, ⁅B, C⁆⁆ := by
      have h1 : S.rightHom A = StableE.natElementary i m h_im a := hA
      have h2 : S.rightHom ⁅B, C⁆ = StableE.natElementary m j h_mj (1 : R) := hBC
      have h_gen := centralLiftGenerator_eq_commutator (R := R) (N := N) (E := E)
          (hS := hS) i j hij a A ⁅B, C⁆ h1 h2
      exact h_gen
    have h_AC' : ⁅A, C⁆ = 1 := by
      exact distant_lift_comm hS i m k j h_im hkj hij h_mk a (1 : R) A C hA hC
    have h_AB_BC : ⁅⁅A, B⁆, ⁅B, C⁆⁆ = 1 := by
      have h1 : i ≠ j := hij
      have h2 : k ≠ m := Ne.symm h_mk
      exact distant_lift_comm hS i k m j hik h_mj h1 h2 a (1 : R) ⁅A, B⁆ ⁅B, C⁆ hAB hBC
    have h_ABC_BC : ⁅⁅⁅A, B⁆, C⁆, ⁅B, C⁆⁆ = 1 := by
      have h1 : i ≠ j := hij
      have h_jm : j ≠ m := by omega
      have hABC : S.rightHom ⁅⁅A, B⁆, C⁆ = StableE.natElementary i j hij a := by
        have h_map : S.rightHom ⁅⁅A, B⁆, C⁆ = ⁅S.rightHom ⁅A, B⁆, S.rightHom C⁆ :=
          map_commutatorElement S.rightHom ⁅A, B⁆ C
        rw [h_map, hAB, hC]
        have hchev2 : ⁅StableE.natElementary i k hik a, StableE.natElementary k j hkj (1 : R)⁆
            = StableE.natElementary i j hij a := by
          have h := StableE.natElementary_chev i k j hik hkj hij a (1 : R)
          simpa [mul_one] using h
        rw [hchev2]
      exact distant_lift_comm hS i j m j hij h_mj h1 h_jm a (1 : R) ⁅⁅A, B⁆, C⁆ ⁅B, C⁆ hABC hBC
    have h_bridge := hallWittBridge A B C h_AC' h_AB_BC h_ABC_BC
    calc centralLiftGenerator (R := R) (N := N) (E := E) S ⟨i, j, hij, a⟩
        = ⁅A, ⁅B, C⁆⁆ := h_canonical
      _ = ⁅⁅A, B⁆, C⁆ := h_bridge.symm
      _ = ⁅u, v⁆ := h_arbitrary.symm

/-- Additivity of lifted generators: `g(a) * g(b) = g(a + b)` at the
canonical auxiliary index `m = max i j + 1`. -/
theorem centralLiftGenerator_add
    {S : GroupExtension N E (StableE R)} (hS : S.IsCentral)
    (i j : ℕ) (hij : i ≠ j) (a b : R) :
    centralLiftGenerator S ⟨i, j, hij, a⟩ * centralLiftGenerator S ⟨i, j, hij, b⟩ =
      centralLiftGenerator (R := R) (N := N) (E := E) S ⟨i, j, hij, a + b⟩ := by
  let m := max i j + 1
  have hm_gt_i : i < m := by
    have : i ≤ max i j := Nat.le_max_left i j
    omega
  have hm_gt_j : j < m := by
    have : j ≤ max i j := Nat.le_max_right i j
    omega
  have h_im : i ≠ m := Nat.ne_of_lt hm_gt_i
  have h_mj : m ≠ j := Nat.ne_of_gt hm_gt_j
  let A : E := S.surjInvRightHom (StableE.natElementary i m h_im a)
  let B : E := S.surjInvRightHom (StableE.natElementary i m h_im b)
  let C : E := S.surjInvRightHom (StableE.natElementary m j h_mj (1 : R))
  have hA : S.rightHom A = StableE.natElementary i m h_im a :=
    S.surjInvRightHom.rightInverse_rightHom (StableE.natElementary i m h_im a)
  have hB : S.rightHom B = StableE.natElementary i m h_im b :=
    S.surjInvRightHom.rightInverse_rightHom (StableE.natElementary i m h_im b)
  have hC : S.rightHom C = StableE.natElementary m j h_mj (1 : R) :=
    S.surjInvRightHom.rightInverse_rightHom (StableE.natElementary m j h_mj (1 : R))
  have hBA_img : S.rightHom (B * A) = StableE.natElementary i m h_im (a + b) := by
    have h_map : S.rightHom (B * A) = S.rightHom B * S.rightHom A :=
      map_mul S.rightHom B A
    rw [h_map, hB, hA]
    have h_add : StableE.natElementary i m h_im b * StableE.natElementary i m h_im a
        = StableE.natElementary i m h_im (b + a) := StableE.natElementary_add i m h_im b a
    have h_comm : (b + a : R) = a + b := add_comm b a
    rw [h_add, h_comm]
  have h_gen_a : centralLiftGenerator (R := R) (N := N) (E := E) S ⟨i, j, hij, a⟩ = ⁅A, C⁆ := by
    exact centralLiftGenerator_eq_commutator hS i j hij a A C hA hC
  have h_gen_b : centralLiftGenerator (R := R) (N := N) (E := E) S ⟨i, j, hij, b⟩ = ⁅B, C⁆ := by
    exact centralLiftGenerator_eq_commutator hS i j hij b B C hB hC
  have h_genBA :
      centralLiftGenerator (R := R) (N := N) (E := E) S ⟨i, j, hij, a + b⟩ =
        ⁅B * A, C⁆ := by
    have hBA : S.rightHom (B * A) = StableE.natElementary i m h_im (a + b) := hBA_img
    exact centralLiftGenerator_eq_commutator hS i j hij (a + b) (B * A) C hBA hC
  have h_B_AC : ⁅B, ⁅A, C⁆⁆ = 1 := by
    have hAC_img : S.rightHom ⁅A, C⁆ = StableE.natElementary i j hij a := by
      have h_map : S.rightHom ⁅A, C⁆ = ⁅S.rightHom A, S.rightHom C⁆ :=
        map_commutatorElement S.rightHom A C
      rw [h_map, hA, hC]
      have hchev : ⁅StableE.natElementary i m h_im a, StableE.natElementary m j h_mj (1 : R)⁆
          = StableE.natElementary i j hij a := by
        have h := StableE.natElementary_chev i m j h_im h_mj hij a (1 : R)
        simpa [mul_one] using h
      rw [hchev]
    have h_mi : m ≠ i := Ne.symm h_im
    exact distant_lift_comm hS i m i j h_im hij hij h_mi b a B ⁅A, C⁆ hB hAC_img
  have h_expand_BA : ⁅B * A, C⁆ = B * ⁅A, C⁆ * B⁻¹ * ⁅B, C⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul]
  have h_B_conj : B * ⁅A, C⁆ * B⁻¹ = ⁅A, C⁆ := by
    have h_comm : Commute B ⁅A, C⁆ :=
      (commutatorElement_eq_one_iff_commute.mp h_B_AC)
    exact h_comm.mul_inv_cancel
  have h_BA_eq : ⁅B * A, C⁆ = ⁅A, C⁆ * ⁅B, C⁆ := by
    rw [h_expand_BA, h_B_conj]
  calc centralLiftGenerator S ⟨i, j, hij, a⟩ * centralLiftGenerator S ⟨i, j, hij, b⟩
      = ⁅A, C⁆ * ⁅B, C⁆ := by rw [h_gen_a, h_gen_b]
    _ = ⁅B * A, C⁆ := by rw [← h_BA_eq]
    _ = centralLiftGenerator (R := R) (N := N) (E := E) S ⟨i, j, hij, a + b⟩ := by
        rw [← h_genBA]

/-- Distant commutativity for lifted generators: disjoint index sets give
trivial commutator. -/
theorem centralLiftGenerator_comm
    {S : GroupExtension N E (StableE R)} (hS : S.IsCentral)
    (i j k l : ℕ) (hij : i ≠ j) (hkl : k ≠ l) (hil : i ≠ l) (hjk : j ≠ k)
    (a b : R) :
    ⁅centralLiftGenerator (R := R) (N := N) (E := E) S ⟨i, j, hij, a⟩,
      centralLiftGenerator S ⟨k, l, hkl, b⟩⁆ = 1 := by
  have h_right_a : S.rightHom (centralLiftGenerator S ⟨i, j, hij, a⟩) =
      StableE.natElementary i j hij a := rightHom_centralLiftGenerator S i j hij a
  have h_right_b : S.rightHom (centralLiftGenerator S ⟨k, l, hkl, b⟩) =
      StableE.natElementary k l hkl b := rightHom_centralLiftGenerator S k l hkl b
  exact distant_lift_comm hS i j k l hij hkl hil hjk a b
    (centralLiftGenerator S ⟨i, j, hij, a⟩) (centralLiftGenerator S ⟨k, l, hkl, b⟩)
    h_right_a h_right_b

/-- Chevalley relation for lifted generators: `⁅g(i,j,a), g(j,k,b)⁆ = g(i,k, a*b)`. -/
theorem centralLiftGenerator_chev
    {S : GroupExtension N E (StableE R)} (hS : S.IsCentral)
    (i j k : ℕ) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    ⁅centralLiftGenerator (R := R) (N := N) (E := E) S ⟨i, j, hij, a⟩,
      centralLiftGenerator S ⟨j, k, hjk, b⟩⁆ =
      centralLiftGenerator S ⟨i, k, hik, a * b⟩ := by
  let l := max (max i j) k + 2
  have hl_gt_i : i < l := by
    have : i ≤ max i j := Nat.le_max_left i j
    have : max i j ≤ max (max i j) k := Nat.le_max_left _ _
    omega
  have hl_gt_j : j < l := by
    have : j ≤ max i j := Nat.le_max_right i j
    have : max i j ≤ max (max i j) k := Nat.le_max_left _ _
    omega
  have hl_gt_k : k < l := by
    have : k ≤ max (max i j) k := Nat.le_max_right _ _
    omega
  have h_jl : j ≠ l := Nat.ne_of_lt hl_gt_j
  have h_lk : l ≠ k := Nat.ne_of_gt hl_gt_k
  have h_il : i ≠ l := Nat.ne_of_lt hl_gt_i
  let B : E := S.surjInvRightHom (StableE.natElementary j l h_jl b)
  let C : E := S.surjInvRightHom (StableE.natElementary l k h_lk (1 : R))
  have hB : S.rightHom B = StableE.natElementary j l h_jl b :=
    S.surjInvRightHom.rightInverse_rightHom (StableE.natElementary j l h_jl b)
  have hC : S.rightHom C = StableE.natElementary l k h_lk (1 : R) :=
    S.surjInvRightHom.rightInverse_rightHom (StableE.natElementary l k h_lk (1 : R))
  let A : E := centralLiftGenerator (R := R) (N := N) (E := E) S ⟨i, j, hij, a⟩
  have hA : S.rightHom A = StableE.natElementary i j hij a :=
    rightHom_centralLiftGenerator S i j hij a
  have h_jk_chev : ⁅StableE.natElementary j l h_jl b, StableE.natElementary l k h_lk (1 : R)⁆
      = StableE.natElementary j k hjk b := by
    have h := StableE.natElementary_chev j l k h_jl h_lk hjk b (1 : R)
    simpa [mul_one] using h
  have hBC : S.rightHom ⁅B, C⁆ = StableE.natElementary j k hjk b := by
    have h_map : S.rightHom ⁅B, C⁆ = ⁅S.rightHom B, S.rightHom C⁆ :=
      map_commutatorElement S.rightHom B C
    rw [h_map, hB, hC, h_jk_chev]
  let Gjk : E := centralLiftGenerator (R := R) (N := N) (E := E) S ⟨j, k, hjk, b⟩
  have hGjk : S.rightHom Gjk = StableE.natElementary j k hjk b :=
    rightHom_centralLiftGenerator S j k hjk b
  have h_left_eq : ⁅A, Gjk⁆ = ⁅A, ⁅B, C⁆⁆ := by
    apply hS.commutator_eq_of_rightHom_eq
    · rfl
    · rw [hBC, hGjk]
  have h_AC : ⁅A, C⁆ = 1 := by
    have h1 : i ≠ k := hik
    have h2 : j ≠ l := h_jl
    exact distant_lift_comm hS i j l k hij h_lk h1 h2 a (1 : R) A C hA hC
  have h_il_chev : ⁅StableE.natElementary i j hij a, StableE.natElementary j l h_jl b⁆
      = StableE.natElementary i l h_il (a * b) := by
    have h := StableE.natElementary_chev i j l hij h_jl h_il a b
    simpa using h
  have hAB : S.rightHom ⁅A, B⁆ = StableE.natElementary i l h_il (a * b) := by
    have h_map : S.rightHom ⁅A, B⁆ = ⁅S.rightHom A, S.rightHom B⁆ :=
      map_commutatorElement S.rightHom A B
    rw [h_map, hA, hB, h_il_chev]
  have h_AB_BC : ⁅⁅A, B⁆, ⁅B, C⁆⁆ = 1 := by
    have hBC_img : S.rightHom ⁅B, C⁆ = StableE.natElementary j k hjk b := hBC
    exact distant_lift_comm hS i l j k h_il hjk hik (by omega) (a * b) b ⁅A, B⁆ ⁅B, C⁆ hAB hBC_img
  have h_ABC : S.rightHom ⁅⁅A, B⁆, C⁆ = StableE.natElementary i k hik (a * b) := by
    have h_map : S.rightHom ⁅⁅A, B⁆, C⁆ = ⁅S.rightHom ⁅A, B⁆, S.rightHom C⁆ :=
      map_commutatorElement S.rightHom ⁅A, B⁆ C
    rw [h_map, hAB, hC]
    have hchev : ⁅StableE.natElementary i l h_il (a * b), StableE.natElementary l k h_lk (1 : R)⁆
        = StableE.natElementary i k hik (a * b) := by
      have h := StableE.natElementary_chev i l k h_il h_lk hik (a * b) (1 : R)
      simpa [mul_one] using h
    rw [hchev]
  have h_ABC_BC : ⁅⁅⁅A, B⁆, C⁆, ⁅B, C⁆⁆ = 1 := by
    have h1 : i ≠ k := hik
    have h2 : k ≠ j := Ne.symm hjk
    exact distant_lift_comm hS i k j k hik hjk h1 h2 (a * b) b ⁅⁅A, B⁆, C⁆ ⁅B, C⁆ h_ABC hBC
  have h_bridge := hallWittBridge A B C h_AC h_AB_BC h_ABC_BC
  have h_right : ⁅⁅A, B⁆, C⁆ =
      centralLiftGenerator (R := R) (N := N) (E := E) S ⟨i, k, hik, a * b⟩ := by
    have h_aux := centralLiftGenerator_eq_commutator_of_aux (R := R) (N := N) (E := E)
        (hS := hS) i k l hik h_il h_lk (a * b) ⁅A, B⁆ C hAB hC
    exact h_aux.symm
  calc ⁅A, Gjk⁆ = ⁅A, ⁅B, C⁆⁆ := h_left_eq
    _ = ⁅⁅A, B⁆, C⁆ := h_bridge.symm
    _ = centralLiftGenerator S ⟨i, k, hik, a * b⟩ := h_right

end StableSteinberg

end AlgebraicKTheory

end

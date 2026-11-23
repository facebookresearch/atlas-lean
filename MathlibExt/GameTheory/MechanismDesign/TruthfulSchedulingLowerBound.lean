/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.GameTheory.MechanismDesign.TruthfulScheduling

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The factor-2 lower bound for truthful scheduling

No deterministic truthful mechanism for unrelated-machine scheduling
approximates the makespan within any factor `c < 2`: for every such
`c` there is a number of tasks (on two machines) at which every
truthful allocation rule fails to be a `c`-approximation. The proof
perturbs the smaller side of the all-ones instance and uses weak
monotonicity to keep the allocation fixed while the optimum drops
toward half of the mechanism's makespan.

References: N. Nisan and A. Ronen, "Algorithmic mechanism design",
*Games and Economic Behavior* 35 (2001), 166–196, §4.3.2,
Theorem 4.6; *Algorithmic Game Theory* (Nisan, Roughgarden, Tardos
and Vazirani, eds.), Chapter 12, Exercise 12.2 (the weak-monotonicity
route).
-/

set_option autoImplicit false

namespace MathlibExt.GameTheory.MechanismDesign.TruthfulScheduling

@[expose] public section

private theorem optMakespan_nonneg {m : ℕ} (t : Fin 2 → Fin m → ℝ)
    (ht : ∀ i j, 0 ≤ t i j) : 0 ≤ optMakespan t := by
  have hmem : optMakespan t ∈
      (Finset.univ : Finset (Fin m → Fin 2)).image (makespanOf t) := by
    unfold optMakespan
    exact Finset.min'_mem _ _
  rw [Finset.mem_image] at hmem
  obtain ⟨A0, _, hA0⟩ := hmem
  have h1 : (0:ℝ) ≤ load t A0 0 := load_nonneg ht A0 0
  have h2 : load t A0 0 ≤ makespanOf t A0 := load_le_makespanOf t A0 0
  linarith

private theorem branch_false {c : ℝ} (hc : c < 2) {N : ℕ}
    (hN : 1 ≤ N) (hNc : c < (N : ℝ) * (2 - c))
    (A : (Fin 2 → Fin (2 * N) → ℝ) → Fin (2 * N) → Fin 2)
    (_P : (Fin 2 → Fin (2 * N) → ℝ) → Fin 2 → ℝ)
    (hW : IsWeaklyMonotone A) (hAp : IsApproximate c A)
    (i j : Fin 2) (hij : j ≠ i)
    (hle : (Finset.univ.filter (fun t => A (fun _ _ => (1:ℝ)) t = i)).card ≤
      (Finset.univ.filter (fun t => A (fun _ _ => (1:ℝ)) t = j)).card) :
    False := by
  have hne_ji : j ≠ i := hij
  have hne_ij : i ≠ j := hij.symm
  have h2c : (0:ℝ) < 2 - c := by linarith
  have hNnn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg _
  have hNpos : (0:ℝ) < (N:ℝ) := by
    have h0N : 0 < N := hN
    exact_mod_cast h0N
  set t0 : Fin 2 → Fin (2 * N) → ℝ := fun _ _ => (1:ℝ) with ht0
  set X : Finset (Fin (2 * N)) := Finset.univ.filter (fun t => A t0 t = i) with hX
  set Y : Finset (Fin (2 * N)) := Finset.univ.filter (fun t => A t0 t = j) with hY
  have hcard2 : ({i, j} : Finset (Fin 2)).card = 2 := Finset.card_pair hne_ij
  have huniv2 : ({i, j} : Finset (Fin 2)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard2]; exact (Fintype.card_fin 2).symm)
  have hcov : ∀ k : Fin 2, k = i ∨ k = j := by
    intro k
    have hk : k ∈ ({i, j} : Finset (Fin 2)) := by
      rw [huniv2]
      exact Finset.mem_univ k
    rwa [Finset.mem_insert, Finset.mem_singleton] at hk
  have hmem_cover : ∀ t, t ∈ X ∨ t ∈ Y := by
    intro t
    rw [hX, hY]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hcov (A t0 t)
  have hunion : X ∪ Y = Finset.univ := by
    ext t
    simp only [Finset.mem_union, Finset.mem_univ]
    exact iff_of_true (hmem_cover t) trivial
  have hdisjXY : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro t htX htY
    rw [hX] at htX
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at htX
    rw [hY] at htY
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at htY
    exact hne_ji (htY.symm.trans htX)
  have hpart : X.card + Y.card = 2 * N := by
    have h1 := Finset.card_union_of_disjoint hdisjXY
    rw [hunion, Finset.card_univ, Fintype.card_fin] at h1
    exact h1.symm
  have hYge : N ≤ Y.card := by omega
  have hY1 : 1 ≤ Y.card := by omega
  have hYpos : (0:ℝ) < (Y.card:ℝ) := by
    have h0Y : 0 < Y.card := hY1
    exact_mod_cast h0Y
  have hYN : (N:ℝ) ≤ (Y.card:ℝ) := by exact_mod_cast hYge
  obtain ⟨ε, hε0, hε1, hεkey⟩ :
      ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
        c * ((Y.card:ℝ)/2 + 1/2 + ε*(2*(N:ℝ))) < (Y.card:ℝ) := by
    by_cases hcpos : 0 < c
    · have hY : c < (Y.card:ℝ) * (2 - c) :=
        lt_of_lt_of_le hNc (mul_le_mul_of_nonneg_right hYN (le_of_lt h2c))
      have hgap : c * ((Y.card:ℝ)/2 + 1/2) < (Y.card:ℝ) := by linarith [hY]
      set δ : ℝ := (Y.card:ℝ) - c * ((Y.card:ℝ)/2 + 1/2) with hδ
      have hδpos : 0 < δ := by
        rw [hδ]
        linarith [hgap]
      have hCK : (0:ℝ) < c * (2*(N:ℝ)) := mul_pos hcpos (by linarith)
      have hCK1 : (0:ℝ) < c * (2*(N:ℝ)) + 1 := by linarith [hCK]
      have hbound : (0:ℝ) < min 1 (δ / (c * (2*(N:ℝ)) + 1)) := by
        rw [lt_min_iff]
        exact ⟨by linarith, div_pos hδpos hCK1⟩
      obtain ⟨ε, hε0, hεlt⟩ := exists_between hbound
      have hε1 : ε < 1 := lt_of_lt_of_le hεlt (min_le_left _ _)
      have hεδ : ε < δ / (c * (2*(N:ℝ)) + 1) := lt_of_lt_of_le hεlt (min_le_right _ _)
      have h1 : ε * (c * (2*(N:ℝ))) < δ := by
        have h2 : (δ / (c*(2*(N:ℝ))+1)) * (c*(2*(N:ℝ))) < δ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ hCK1]
          have h3 : δ * (c*(2*(N:ℝ))+1) = δ * (c*(2*(N:ℝ))) + δ := by
            rw [mul_add, mul_one]
          linarith [h3, hδpos]
        have h4 : ε * (c*(2*(N:ℝ))) < (δ / (c*(2*(N:ℝ))+1)) * (c*(2*(N:ℝ))) :=
          mul_lt_mul_of_pos_right hεδ hCK
        exact lt_trans h4 h2
      refine ⟨ε, hε0, hε1, ?_⟩
      linarith [h1, hδ]
    · have hc0 : c ≤ 0 := le_of_not_gt hcpos
      refine ⟨1/2, by linarith, by linarith, ?_⟩
      have hinner : (0:ℝ) ≤ (Y.card:ℝ)/2 + 1/2 + (1/2)*(2*(N:ℝ)) := by
        linarith [hYpos, hNnn]
      have hmul : c * ((Y.card:ℝ)/2 + 1/2 + (1/2)*(2*(N:ℝ))) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hc0 hinner
      linarith [hmul, hYpos]
  set t1 : Fin 2 → Fin (2 * N) → ℝ :=
    Function.update t0 i (fun t => if A t0 t = i then ε else 1 + ε) with ht1
  have ht0nonneg : ∀ k t, 0 ≤ t0 k t := by
    intro k t
    rw [ht0]
    show (0:ℝ) ≤ 1
    linarith
  have ht1row : ∀ k ≠ i, t1 k = t0 k := by
    intro k hk
    rw [ht1]
    exact Function.update_of_ne hk _ _
  have ht1i : t1 i = fun t => if A t0 t = i then ε else 1 + ε := by
    rw [ht1]
    exact Function.update_self i _ _
  have ht1nonneg : ∀ k t, 0 ≤ t1 k t := by
    intro k t
    by_cases hk : k = i
    · rw [hk, ht1i]
      show (0:ℝ) ≤ (if A t0 t = i then ε else 1 + ε)
      by_cases h : A t0 t = i
      · simp [h]
        exact le_of_lt hε0
      · simp [h]
        linarith [hε0]
    · rw [ht1row k hk, ht0]
      show (0:ℝ) ≤ 1
      linarith
  have ht1j : ∀ t, t1 j t = 1 := by
    intro t
    have hrow : t1 j = t0 j := ht1row j hij
    simp [hrow, ht0]
  set X' : Finset (Fin (2 * N)) := Finset.univ.filter (fun t => A t1 t = i) with hX'
  have hpt_i : ∀ t ∈ X, t1 i t = ε := by
    intro t ht
    have ht_i : A t0 t = i := by
      rw [hX] at ht
      exact (Finset.mem_filter.mp ht).2
    simp [ht1i, ht_i]
  have hdisj : Disjoint (X' \ X) (X ∩ X') := by
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    exact (Finset.mem_sdiff.mp ht1).2 (Finset.mem_inter.mp ht2).1
  have hsplit : X' = (X' \ X) ∪ (X ∩ X') := by
    rw [Finset.inter_comm X X']
    exact (Finset.sdiff_union_inter X' X).symm
  have hL1 : load t0 (A t0) i = (X.card:ℝ) := by
    unfold load
    rw [← hX]
    simp only [ht0, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hL2 : load t0 (A t1) i = (X'.card:ℝ) := by
    unfold load
    rw [← hX']
    simp only [ht0, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hL3 : load t1 (A t0) i = ε * (X.card:ℝ) := by
    unfold load
    rw [← hX]
    rw [Finset.sum_congr rfl hpt_i, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hL4 : load t1 (A t1) i =
      ε * ((X ∩ X').card:ℝ) + (1+ε) * ((X' \ X).card:ℝ) := by
    unfold load
    rw [← hX']
    conv => lhs; rw [hsplit]
    rw [Finset.sum_union hdisj]
    have hpt1 : ∀ t ∈ X' \ X, t1 i t = 1 + ε := by
      intro t ht
      have ht_ne : A t0 t ≠ i := by
        intro hcon
        have hmem : t ∈ X := by
          rw [hX]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hcon
        exact (Finset.mem_sdiff.mp ht).2 hmem
      rw [ht1i]
      simp [ht_ne]
    have hpt2 : ∀ t ∈ X ∩ X', t1 i t = ε := by
      intro t ht
      have ht_i : A t0 t = i := by
        have hmem : t ∈ X := (Finset.mem_inter.mp ht).1
        rw [hX] at hmem
        exact (Finset.mem_filter.mp hmem).2
      rw [ht1i]
      simp [ht_i]
    rw [Finset.sum_congr rfl hpt1, Finset.sum_congr rfl hpt2]
    rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    ring
  have hcardX : ((X \ X').card:ℝ) + ((X ∩ X').card:ℝ) = (X.card:ℝ) := by
    have h := Finset.sdiff_union_inter X X'
    have hd : Disjoint (X \ X') (X ∩ X') := by
      rw [Finset.disjoint_left]
      intro t ht1 ht2
      exact (Finset.mem_sdiff.mp ht1).2 (Finset.mem_inter.mp ht2).2
    have hc := Finset.card_union_of_disjoint hd
    rw [h] at hc
    exact_mod_cast hc.symm
  have hcardX' : ((X' \ X).card:ℝ) + ((X ∩ X').card:ℝ) = (X'.card:ℝ) := by
    have h := Finset.sdiff_union_inter X' X
    rw [Finset.inter_comm X' X] at h
    have hc := Finset.card_union_of_disjoint hdisj
    rw [h] at hc
    exact_mod_cast hc.symm
  have hlink : ε * (X.card:ℝ) =
      ε * ((X \ X').card:ℝ) + ε * ((X ∩ X').card:ℝ) := by
    rw [← hcardX, mul_add]
  have hWM := hW t0 t1 ht0nonneg ht1nonneg i ht1row
  have ha0 : (((X \ X').card : ℕ):ℝ) = 0 := by
    have h2 : ε * (((X' \ X).card:ℕ):ℝ) ≥ 0 :=
      mul_nonneg (le_of_lt hε0) (Nat.cast_nonneg _)
    have hnm : (((X \ X').card:ℕ):ℝ) * (1 - ε) ≤ 0 := by
      linarith [hWM, hL1, hL2, hL3, hL4, hcardX, hcardX', hlink, h2]
    by_contra hne
    have hapos : (0:ℝ) < ((X \ X').card:ℕ) :=
      lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hne)
    have hpos := mul_pos hapos (show (0:ℝ) < 1 - ε by linarith)
    linarith [hnm, hpos]
  have hb0 : (((X' \ X).card:ℕ):ℝ) = 0 := by
    have hεa0 : ε * (((X \ X').card:ℕ):ℝ) = 0 := by rw [ha0, mul_zero]
    have hle : ε * (((X' \ X).card:ℕ):ℝ) ≤ 0 := by
      linarith [hWM, hL1, hL2, hL3, hL4, hcardX, hcardX', hlink, ha0, hεa0]
    by_contra hne
    have hbpos : (0:ℝ) < ((X' \ X).card:ℕ) :=
      lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hne)
    have hpos := mul_pos hε0 hbpos
    linarith [hle, hpos]
  have hX'X : X' = X := by
    have hsub1 : X ⊆ X' := by
      rw [← Finset.sdiff_eq_empty_iff_subset]
      rw [← Finset.card_eq_zero]
      exact_mod_cast ha0
    have hsub2 : X' ⊆ X := by
      rw [← Finset.sdiff_eq_empty_iff_subset]
      rw [← Finset.card_eq_zero]
      exact_mod_cast hb0
    exact le_antisymm hsub2 hsub1
  have hY' : Finset.univ.filter (fun t => A t1 t = j) = Y := by
    ext t
    rw [hY]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hi1 : A t1 t = i ↔ A t0 t = i := by
      have hmem : t ∈ X' ↔ t ∈ X := by rw [hX'X]
      rw [hX', hX] at hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact hmem
    constructor
    · intro hr
      have hni : A t1 t ≠ i := fun hp => hne_ij (hp.symm.trans hr)
      have hni0 : A t0 t ≠ i := fun hp => hni (hi1.mpr hp)
      rcases hcov (A t0 t) with h | h
      · exact absurd h hni0
      · exact h
    · intro hr
      have hni : A t0 t ≠ i := fun hp => hne_ij (hp.symm.trans hr)
      have hni1 : A t1 t ≠ i := fun hp => hni (hi1.mp hp)
      rcases hcov (A t1 t) with h | h
      · exact absurd h hni1
      · exact h
  have hload_i : load t1 (A t1) i = ε * (X.card:ℝ) := by
    unfold load
    rw [← hX', hX'X]
    rw [Finset.sum_congr rfl hpt_i, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hload_j : load t1 (A t1) j = (Y.card:ℝ) := by
    unfold load
    rw [hY']
    have hpt : ∀ t ∈ Y, t1 j t = 1 := fun t _ => ht1j t
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hload_i_le : load t1 (A t1) i ≤ (Y.card:ℝ) := by
    rw [hload_i]
    have h1 : ε * (X.card:ℝ) ≤ 1 * (X.card:ℝ) :=
      mul_le_mul_of_nonneg_right (le_of_lt hε1) (Nat.cast_nonneg _)
    have h2 : (X.card:ℝ) ≤ (Y.card:ℝ) := by exact_mod_cast hle
    linarith [h1, h2]
  have hmake_eq : makespanOf t1 (A t1) = (Y.card:ℝ) := by
    apply le_antisymm
    · unfold makespanOf
      apply Finset.max'_le
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨k, _, rfl⟩ := hy
      rcases hcov k with rfl | rfl
      · exact hload_i_le
      · exact le_of_eq hload_j
    · rw [← hload_j]
      exact load_le_makespanOf t1 (A t1) j
  obtain ⟨S, hSY, hScard⟩ := Finset.exists_subset_card_eq (s := Y) (n := Y.card / 2) (Nat.div_le_self Y.card 2)
  have hXSle : X.card + S.card ≤ 2 * N := by omega
  have hSle : ((S.card:ℕ):ℝ) ≤ (Y.card:ℝ)/2 := by
    have h2mul : 2 * (Y.card/2) ≤ Y.card := by omega
    have hcast : (2:ℝ) * (((Y.card/2 : ℕ)):ℝ) ≤ ((Y.card:ℕ):ℝ) := by
      exact_mod_cast h2mul
    rw [hScard]
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 2)]
    linarith [hcast]
  have hdisjXS : Disjoint X S := by
    rw [Finset.disjoint_left]
    intro t htX htS
    have htY : t ∈ Y := hSY htS
    have hnot : t ∉ Y := Finset.disjoint_left.mp hdisjXY htX
    exact hnot htY
  set A' : Fin (2 * N) → Fin 2 := fun t => if t ∈ X ∪ S then i else j with hA'
  have hif_i : ∀ t, (if t ∈ X ∪ S then i else j) = i ↔ t ∈ X ∪ S := by
    intro t
    by_cases ht : t ∈ X ∪ S
    · simp [ht]
    · simp [ht, hne_ji]
  have hif_j : ∀ t, (if t ∈ X ∪ S then i else j) = j ↔ t ∉ X ∪ S := by
    intro t
    by_cases ht : t ∈ X ∪ S
    · simp [ht, hne_ij]
    · simp [ht]
  have hAbun_i : Finset.univ.filter (fun t => A' t = i) = X ∪ S := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rw [hA']
    show (if t ∈ X ∪ S then i else j) = i ↔ t ∈ X ∨ t ∈ S
    rw [hif_i t, Finset.mem_union]
  have hAbun_j : Finset.univ.filter (fun t => A' t = j) = Y \ S := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    rw [hA']
    show (if t ∈ X ∪ S then i else j) = j ↔ t ∈ Y ∧ t ∉ S
    rw [hif_j t]
    constructor
    · intro h
      rw [Finset.mem_union] at h
      have hX' : t ∉ X := fun hx => h (Or.inl hx)
      have hS' : t ∉ S := fun hs => h (Or.inr hs)
      refine ⟨?_, hS'⟩
      rw [hY]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hni : A t0 t ≠ i := by
        intro hcon
        apply hX'
        rw [hX]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hcon
      rcases hcov (A t0 t) with hcon | hcon
      · exact absurd hcon hni
      · exact hcon
    · intro h hc
      rw [Finset.mem_union] at hc
      rcases hc with hcX | hcS
      · rw [hX] at hcX
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcX
        rw [hY] at h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
        exact hne_ij (hcX.symm.trans h.1)
      · exact h.2 hcS
  have hloadA'i : load t1 A' i = ε * (X.card:ℝ) + (1+ε) * (S.card:ℝ) := by
    unfold load
    rw [hAbun_i, Finset.sum_union hdisjXS]
    have hptS : ∀ t ∈ S, t1 i t = 1 + ε := by
      intro t ht
      have htY : t ∈ Y := hSY ht
      have ht_j : A t0 t = j := by
        rw [hY] at htY
        exact (Finset.mem_filter.mp htY).2
      have ht_ne : A t0 t ≠ i := by
        intro hcon
        exact hne_ji (ht_j.symm.trans hcon)
      rw [ht1i]
      simp [ht_ne]
    rw [Finset.sum_congr rfl hpt_i, Finset.sum_congr rfl hptS]
    rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    ring
  have hloadA'j : load t1 A' j = ((Y.card:ℕ):ℝ) - ((S.card:ℕ):ℝ) := by
    unfold load
    rw [hAbun_j]
    have hpt : ∀ t ∈ Y \ S, t1 j t = 1 := fun t _ => ht1j t
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard := Finset.card_sdiff_add_card_eq_card hSY
    have hcast : (((Y \ S).card:ℕ):ℝ) + ((S.card:ℕ):ℝ) = ((Y.card:ℕ):ℝ) := by
      exact_mod_cast hcard
    linarith [hcast]
  have hloadA'i_le : load t1 A' i ≤ (Y.card:ℝ)/2 + ε*(2*(N:ℝ)) := by
    rw [hloadA'i]
    have hle_cast : (X.card:ℝ) + (S.card:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast hXSle
    have hmul : ε * ((X.card:ℝ) + (S.card:ℝ)) ≤ ε * (2*(N:ℝ)) :=
      mul_le_mul_of_nonneg_left hle_cast (le_of_lt hε0)
    linarith [hmul, hSle]
  have hloadA'j_le : load t1 A' j ≤ (Y.card:ℝ)/2 + 1/2 := by
    rw [hloadA'j]
    have hYS : Y.card ≤ 2 * S.card + 1 := by omega
    have hcast : ((Y.card:ℕ):ℝ) ≤ 2 * ((S.card:ℕ):ℝ) + 1 := by exact_mod_cast hYS
    linarith [hcast]
  have hmakeA' : makespanOf t1 A' ≤ (Y.card:ℝ)/2 + 1/2 + ε*(2*(N:ℝ)) := by
    unfold makespanOf
    apply Finset.max'_le
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨k, _, rfl⟩ := hy
    rcases hcov k with rfl | rfl
    · linarith [hloadA'i_le]
    · have hnn : (0:ℝ) ≤ ε*(2*(N:ℝ)) := mul_nonneg (le_of_lt hε0) (by linarith [hNnn])
      linarith [hloadA'j_le, hnn]
  have hoptQ : optMakespan t1 ≤ (Y.card:ℝ)/2 + 1/2 + ε*(2*(N:ℝ)) :=
    le_trans (optMakespan_le t1 A') hmakeA'
  have hAp1 := hAp t1 ht1nonneg
  rw [hmake_eq] at hAp1
  by_cases hcpos : 0 < c
  · have hmul : c * optMakespan t1 ≤ c * ((Y.card:ℝ)/2 + 1/2 + ε*(2*(N:ℝ))) :=
      mul_le_mul_of_nonneg_left hoptQ (le_of_lt hcpos)
    linarith [hAp1, hmul, hεkey]
  · have hc0 : c ≤ 0 := le_of_not_gt hcpos
    have hopt_nonneg := optMakespan_nonneg t1 ht1nonneg
    have hmul : c * optMakespan t1 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc0 hopt_nonneg
    linarith [hAp1, hmul, hYpos]

/-- **Nisan–Ronen lower bound (factor 2).** For every `c < 2` there
is a task count `m` such that no truthful mechanism on two machines
with `m` tasks is a `c`-approximation for the makespan. -/
theorem exists_taskCount_not_isApproximate_of_isTruthful_of_lt_two
    {c : ℝ} (hc : c < 2) :
    ∃ m : ℕ, ∀ (A : (Fin 2 → Fin m → ℝ) → Fin m → Fin 2)
      (P : (Fin 2 → Fin m → ℝ) → Fin 2 → ℝ),
      IsTruthful A P → ¬ IsApproximate c A := by
  obtain ⟨n, hn⟩ := exists_nat_gt (c / (2 - c))
  have h2c : (0:ℝ) < 2 - c := by linarith
  have hcn : c < (n:ℝ) * (2 - c) := (div_lt_iff₀ h2c).mp hn
  have hN : 1 ≤ n + 1 := by omega
  have hNc : c < (((n + 1 : ℕ)):ℝ) * (2 - c) := by
    have hle : (n:ℝ) ≤ (((n + 1 : ℕ)):ℝ) := by exact_mod_cast Nat.le_add_right n 1
    have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt h2c)
    linarith [hcn, hmul]
  refine ⟨2 * (n + 1), ?_⟩
  intro A P hTruth hAp
  have hW := isWeaklyMonotone_of_isTruthful hTruth
  by_cases hle : (Finset.univ.filter (fun t => A (fun _ _ => (1:ℝ)) t = 0)).card ≤
      (Finset.univ.filter (fun t => A (fun _ _ => (1:ℝ)) t = 1)).card
  · exact branch_false hc hN hNc A P hW hAp 0 1 (by decide) hle
  · simp only [not_le] at hle
    exact branch_false hc hN hNc A P hW hAp 1 0 (by decide) (le_of_lt hle)

end

end MathlibExt.GameTheory.MechanismDesign.TruthfulScheduling

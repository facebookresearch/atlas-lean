/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































import Code.Inequalities.ReimerButterflyStep
import Code.Inequalities.ReimerClose2
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Mathlib.Combinatorics.SetFamily.Compression.UV

open Finset
open scoped FinsetFamily

namespace StatMech

variable {α : Type*} [DecidableEq α]













theorem rby_card_mul_four_fiber (𝒜 ℬ : Finset (Finset α)) (i : α) :
    𝒜.card * ℬ.card
      = (𝒜.nonMemberSubfamily i).card * (ℬ.nonMemberSubfamily i).card
      + (𝒜.memberSubfamily i).card * (ℬ.nonMemberSubfamily i).card
      + (𝒜.nonMemberSubfamily i).card * (ℬ.memberSubfamily i).card
      + (𝒜.memberSubfamily i).card * (ℬ.memberSubfamily i).card := by
  have hA := card_family_fiber_split 𝒜 i
  have hB := card_family_fiber_split ℬ i
  nlinarith [hA, hB]



theorem rby_dpairsCount_add_member_le_mul (𝒜 ℬ : Finset (Finset α)) (i : α) :
    dpairsCount 𝒜 ℬ
        + (𝒜.memberSubfamily i).card * (ℬ.memberSubfamily i).card
      ≤ 𝒜.card * ℬ.card := by
  have hrec := dpairsCount_fiber_recursion 𝒜 ℬ i
  have h1 := dpairsCount_le_mul (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)
  have h2 := dpairsCount_le_mul (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i)
  have h3 := dpairsCount_le_mul (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i)
  rw [hrec, rby_card_mul_four_fiber 𝒜 ℬ i]
  nlinarith [h1, h2, h3]


theorem rby_mul_sub_dpairsCount_ge_member (𝒜 ℬ : Finset (Finset α)) (i : α) :
    (𝒜.memberSubfamily i).card * (ℬ.memberSubfamily i).card
      ≤ 𝒜.card * ℬ.card - dpairsCount 𝒜 ℬ := by
  have h := rby_dpairsCount_add_member_le_mul 𝒜 ℬ i
  omega









def rbyCexA : Finset (Finset (Fin 2)) := {∅, {0}}


def rbyCexB : Finset (Finset (Fin 2)) := {∅}


theorem rby_downCompress_cexA : Down.compression (0 : Fin 2) rbyCexA = {∅, {0}} := by decide


theorem rby_upCompress_cexB :
    UV.compression ({0} : Finset (Fin 2)) ∅ rbyCexB = {{0}} := by decide


theorem rby_card_boxDoubled_cex : (boxDoubled rbyCexA rbyCexB).card = 2 := by
  rw [card_boxDoubled_eq_dpairsCount]; decide


theorem rby_card_boxDoubled_cex_compressed :
    (boxDoubled (Down.compression (0 : Fin 2) rbyCexA)
      (UV.compression ({0} : Finset (Fin 2)) ∅ rbyCexB)).card = 1 := by
  rw [rby_downCompress_cexA, rby_upCompress_cexB, card_boxDoubled_eq_dpairsCount]; decide


theorem rby_separate_compression_strictly_decreases :
    ∃ (𝒜 ℬ : Finset (Finset (Fin 2))) (i : Fin 2),
      (boxDoubled (Down.compression i 𝒜)
        (UV.compression ({i} : Finset (Fin 2)) ∅ ℬ)).card
        < (boxDoubled 𝒜 ℬ).card :=
  ⟨rbyCexA, rbyCexB, 0, by
    rw [rby_card_boxDoubled_cex, rby_card_boxDoubled_cex_compressed]; norm_num⟩



theorem rby_doubleCompress_not_subset_boxDoubled_separate :
    ¬ (doubleCompress (0 : Fin 2) (boxDoubled rbyCexA rbyCexB)
        ⊆ boxDoubled (Down.compression (0 : Fin 2) rbyCexA)
            (UV.compression ({0} : Finset (Fin 2)) ∅ rbyCexB)) := by
  intro hsub
  have hcard := Finset.card_le_card hsub
  rw [doubleCompress_card, rby_card_boxDoubled_cex,
    rby_card_boxDoubled_cex_compressed] at hcard
  omega









section Weighted

variable [Fintype α]




noncomputable def fwt (w : α → Bool → ℝ) (S : Finset α) : ℝ :=
  ∏ x, w x (decide (x ∈ S))




noncomputable def fwt' (w : α → Bool → ℝ) (i : α) (S : Finset α) : ℝ :=
  ∏ x ∈ univ.erase i, w x (decide (x ∈ S))


lemma fwt_nonneg {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b) (S : Finset α) : 0 ≤ fwt w S :=
  Finset.prod_nonneg (fun x _ => hw x _)


lemma fwt'_nonneg {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b) (i : α) (S : Finset α) :
    0 ≤ fwt' w i S :=
  Finset.prod_nonneg (fun x _ => hw x _)




lemma fwt_of_mem (w : α → Bool → ℝ) {S : Finset α} {i : α} (hi : i ∈ S) :
    fwt w S = w i true * fwt' w i (S.erase i) := by
  unfold fwt fwt'
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  rw [decide_eq_true (by simpa using hi : i ∈ S), mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro x hx
  rw [Finset.mem_erase] at hx
  congr 1
  simp [Finset.mem_erase, hx.1]



lemma fwt_of_notMem (w : α → Bool → ℝ) {S : Finset α} {i : α} (hi : i ∉ S) :
    fwt w S = w i false * fwt' w i S := by
  unfold fwt fwt'
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  rw [decide_eq_false (by simpa using hi : i ∉ S)]
  ring





noncomputable def wdpairs (w : α → Bool → ℝ) (𝒜 ℬ : Finset (Finset α)) : ℝ :=
  ∑ p ∈ (𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2), fwt w p.1 * fwt w p.2




noncomputable def wdpairs' (w : α → Bool → ℝ) (i : α) (𝒜 ℬ : Finset (Finset α)) : ℝ :=
  ∑ p ∈ (𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2), fwt' w i p.1 * fwt' w i p.2



noncomputable def fmarg (w : α → Bool → ℝ) (𝒜 : Finset (Finset α)) : ℝ :=
  ∑ S ∈ 𝒜, fwt w S


noncomputable def fmarg' (w : α → Bool → ℝ) (i : α) (𝒜 : Finset (Finset α)) : ℝ :=
  ∑ S ∈ 𝒜, fwt' w i S










theorem wdpairs_le_mul {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b) (𝒜 ℬ : Finset (Finset α)) :
    wdpairs w 𝒜 ℬ ≤ fmarg w 𝒜 * fmarg w ℬ := by
  unfold wdpairs fmarg
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro p _ _
  exact mul_nonneg (fwt_nonneg hw _) (fwt_nonneg hw _)


theorem wdpairs'_le_mul {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b) (i : α)
    (𝒜 ℬ : Finset (Finset α)) :
    wdpairs' w i 𝒜 ℬ ≤ fmarg' w i 𝒜 * fmarg' w i ℬ := by
  unfold wdpairs' fmarg'
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro p _ _
  exact mul_nonneg (fwt'_nonneg hw _ _) (fwt'_nonneg hw _ _)


theorem wdpairs'_nonneg {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b) (i : α)
    (𝒜 ℬ : Finset (Finset α)) : 0 ≤ wdpairs' w i 𝒜 ℬ := by
  unfold wdpairs'
  refine Finset.sum_nonneg (fun p _ => ?_)
  exact mul_nonneg (fwt'_nonneg hw _ _) (fwt'_nonneg hw _ _)











theorem fmarg_split (w : α → Bool → ℝ) (𝒜 : Finset (Finset α)) (i : α) :
    fmarg w 𝒜
      = w i true * fmarg' w i (𝒜.memberSubfamily i)
      + w i false * fmarg' w i (𝒜.nonMemberSubfamily i) := by
  classical
  unfold fmarg fmarg'
  rw [← Finset.sum_filter_add_sum_filter_not 𝒜 (fun S => i ∈ S)]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  · rw [show 𝒜.memberSubfamily i = (𝒜.filter (fun S => i ∈ S)).image (fun S => S.erase i)
        from ?_]
    · rw [Finset.sum_image ?_]
      · apply Finset.sum_congr rfl
        intro S hS
        rw [Finset.mem_filter] at hS
        rw [fwt_of_mem w hS.2]
      · intro S hS T hT heq
        rw [Finset.mem_coe, Finset.mem_filter] at hS hT
        simp only [] at heq
        rw [← Finset.insert_erase hS.2, ← Finset.insert_erase hT.2, heq]
    · ext S
      simp only [Finset.mem_image, Finset.mem_filter, mem_memberSubfamily]
      constructor
      · rintro ⟨hins, hnotin⟩
        exact ⟨insert i S, ⟨hins, Finset.mem_insert_self _ _⟩, by rw [Finset.erase_insert hnotin]⟩
      · rintro ⟨T, ⟨hT, hiT⟩, rfl⟩
        rw [Finset.insert_erase hiT]
        exact ⟨hT, Finset.notMem_erase _ _⟩
  · apply Finset.sum_congr
    · ext S; simp only [Finset.mem_filter, mem_nonMemberSubfamily]
    · intro S hS
      rw [mem_nonMemberSubfamily] at hS
      rw [fwt_of_notMem w hS.2]









theorem wfiber_notMem_notMem (w : α → Bool → ℝ) (𝒜 ℬ : Finset (Finset α)) (i : α) :
    (∑ p ∈ (((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter
              (fun p => i ∉ p.1 ∧ i ∉ p.2)), fwt w p.1 * fwt w p.2)
    = w i false * w i false * wdpairs' w i (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i) := by
  classical
  unfold wdpairs'
  rw [Finset.mul_sum]
  apply Finset.sum_nbij' (fun p => p) (fun p => p)
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_filter, mem_product, mem_nonMemberSubfamily] at hp ⊢
    obtain ⟨⟨⟨hS, hT⟩, hd⟩, hi1, hi2⟩ := hp
    exact ⟨⟨⟨hS, hi1⟩, hT, hi2⟩, hd⟩
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_filter, mem_product, mem_nonMemberSubfamily] at hp ⊢
    obtain ⟨⟨⟨hS, hi1⟩, hT, hi2⟩, hd⟩ := hp
    exact ⟨⟨⟨hS, hT⟩, hd⟩, hi1, hi2⟩
  · intro p _; rfl
  · intro p _; rfl
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_filter, mem_product] at hp
    obtain ⟨_, hi1, hi2⟩ := hp
    rw [fwt_of_notMem w hi1, fwt_of_notMem w hi2]; ring



theorem wfiber_mem_fst (w : α → Bool → ℝ) (𝒜 ℬ : Finset (Finset α)) (i : α) :
    (∑ p ∈ (((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter (fun p => i ∈ p.1)),
      fwt w p.1 * fwt w p.2)
    = w i true * w i false * wdpairs' w i (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i) := by
  classical
  unfold wdpairs'
  rw [Finset.mul_sum]
  rw [show (((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter (fun p => i ∈ p.1))
        = (((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter
            (fun p => i ∈ p.1 ∧ i ∉ p.2)) from ?_]
  · apply Finset.sum_nbij' (fun p => (p.1.erase i, p.2)) (fun p => (insert i p.1, p.2))
    · rintro ⟨S, T⟩ hp
      simp only [Finset.mem_filter, mem_product] at hp ⊢
      obtain ⟨⟨⟨hS, hT⟩, hd⟩, hi1, hi2⟩ := hp
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [mem_memberSubfamily, insert_erase hi1]; exact ⟨hS, notMem_erase _ _⟩
      · rw [mem_nonMemberSubfamily]; exact ⟨hT, hi2⟩
      · exact hd.mono_left (erase_subset _ _)
    · rintro ⟨S, T⟩ hp
      simp only [Finset.mem_filter, mem_product] at hp ⊢
      obtain ⟨⟨hS, hT⟩, hd⟩ := hp
      rw [mem_memberSubfamily] at hS; rw [mem_nonMemberSubfamily] at hT
      obtain ⟨hSins, hiS⟩ := hS; obtain ⟨hTm, hiT⟩ := hT
      refine ⟨⟨⟨hSins, hTm⟩, ?_⟩, ?_, ?_⟩
      · rw [Finset.disjoint_insert_left]; exact ⟨hiT, hd⟩
      · exact mem_insert_self _ _
      · exact hiT
    · rintro ⟨S, T⟩ hp
      simp only [Finset.mem_filter, mem_product] at hp
      obtain ⟨_, hi1, _⟩ := hp; simp only [insert_erase hi1]
    · rintro ⟨S, T⟩ hp
      simp only [Finset.mem_filter, mem_product] at hp
      obtain ⟨⟨hS, _⟩, _⟩ := hp
      rw [mem_memberSubfamily] at hS; simp only [erase_insert hS.2]
    · rintro ⟨S, T⟩ hp
      simp only [Finset.mem_filter, mem_product] at hp
      obtain ⟨⟨_, hd⟩, hi1, hi2⟩ := hp
      rw [fwt_of_mem w hi1, fwt_of_notMem w hi2]; ring
  · apply Finset.filter_congr
    rintro ⟨S, T⟩ hp
    rw [mem_filter] at hp
    simp only [iff_self_and]
    intro hi1 hi2
    exact (Finset.disjoint_left.mp hp.2 hi1) hi2



theorem wfiber_notMem_mem (w : α → Bool → ℝ) (𝒜 ℬ : Finset (Finset α)) (i : α) :
    (∑ p ∈ (((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter
              (fun p => i ∉ p.1 ∧ i ∈ p.2)), fwt w p.1 * fwt w p.2)
    = w i false * w i true * wdpairs' w i (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i) := by
  classical
  unfold wdpairs'
  rw [Finset.mul_sum]
  apply Finset.sum_nbij' (fun p => (p.1, p.2.erase i)) (fun p => (p.1, insert i p.2))
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_filter, mem_product] at hp ⊢
    obtain ⟨⟨⟨hS, hT⟩, hd⟩, hi1, hi2⟩ := hp
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [mem_nonMemberSubfamily]; exact ⟨hS, hi1⟩
    · rw [mem_memberSubfamily, insert_erase hi2]; exact ⟨hT, notMem_erase _ _⟩
    · exact hd.mono_right (erase_subset _ _)
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_filter, mem_product] at hp ⊢
    obtain ⟨⟨hS, hT⟩, hd⟩ := hp
    rw [mem_nonMemberSubfamily] at hS; rw [mem_memberSubfamily] at hT
    obtain ⟨hSm, hiS⟩ := hS; obtain ⟨hTins, hiT⟩ := hT
    refine ⟨⟨⟨hSm, hTins⟩, ?_⟩, ?_, ?_⟩
    · rw [Finset.disjoint_insert_right]; exact ⟨hiS, hd⟩
    · exact hiS
    · exact mem_insert_self _ _
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_filter, mem_product] at hp
    obtain ⟨_, _, hi2⟩ := hp; simp only [insert_erase hi2]
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_filter, mem_product] at hp
    obtain ⟨⟨_, hT⟩, _⟩ := hp
    rw [mem_memberSubfamily] at hT; simp only [erase_insert hT.2]
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_filter, mem_product] at hp
    obtain ⟨⟨_, hd⟩, hi1, hi2⟩ := hp
    rw [fwt_of_notMem w hi1, fwt_of_mem w hi2]; ring



















theorem wdpairs_fiber_recursion (w : α → Bool → ℝ) (𝒜 ℬ : Finset (Finset α)) (i : α) :
    wdpairs w 𝒜 ℬ
      = w i false * w i false * wdpairs' w i (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)
      + w i true * w i false * wdpairs' w i (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i)
      + w i false * w i true * wdpairs' w i (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i) := by
  classical
  unfold wdpairs
  set D := (𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2) with hD
  have hsplit1 :
      (∑ p ∈ D.filter (fun p => i ∈ p.1), fwt w p.1 * fwt w p.2)
        + (∑ p ∈ D.filter (fun p => i ∉ p.1), fwt w p.1 * fwt w p.2)
      = ∑ p ∈ D, fwt w p.1 * fwt w p.2 :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hsplit2 :
      (∑ p ∈ (D.filter (fun p => i ∉ p.1)).filter (fun p => i ∈ p.2), fwt w p.1 * fwt w p.2)
        + (∑ p ∈ (D.filter (fun p => i ∉ p.1)).filter (fun p => i ∉ p.2), fwt w p.1 * fwt w p.2)
      = ∑ p ∈ D.filter (fun p => i ∉ p.1), fwt w p.1 * fwt w p.2 :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have e1 : (D.filter (fun p => i ∉ p.1)).filter (fun p => i ∈ p.2)
          = D.filter (fun p => i ∉ p.1 ∧ i ∈ p.2) := by rw [Finset.filter_filter]
  have e2 : (D.filter (fun p => i ∉ p.1)).filter (fun p => i ∉ p.2)
          = D.filter (fun p => i ∉ p.1 ∧ i ∉ p.2) := by rw [Finset.filter_filter]
  rw [e1, e2] at hsplit2
  rw [← hsplit1, ← hsplit2]
  rw [wfiber_mem_fst w 𝒜 ℬ i, wfiber_notMem_mem w 𝒜 ℬ i, wfiber_notMem_notMem w 𝒜 ℬ i]
  ring


















theorem wdpairs_add_member_le_mul {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b)
    (𝒜 ℬ : Finset (Finset α)) (i : α) :
    wdpairs w 𝒜 ℬ
        + w i true * w i true
            * wdpairs' w i (𝒜.memberSubfamily i) (ℬ.memberSubfamily i)
      ≤ fmarg w 𝒜 * fmarg w ℬ := by
  have hrec := wdpairs_fiber_recursion w 𝒜 ℬ i
  have hA := fmarg_split w 𝒜 i
  have hB := fmarg_split w ℬ i
  have hNN := wdpairs'_le_mul hw i (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)
  have hMN := wdpairs'_le_mul hw i (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i)
  have hNM := wdpairs'_le_mul hw i (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i)
  have hMM := wdpairs'_le_mul hw i (𝒜.memberSubfamily i) (ℬ.memberSubfamily i)
  set w0 := w i false
  set w1 := w i true
  set Am := fmarg' w i (𝒜.memberSubfamily i)
  set An := fmarg' w i (𝒜.nonMemberSubfamily i)
  set Bm := fmarg' w i (ℬ.memberSubfamily i)
  set Bn := fmarg' w i (ℬ.nonMemberSubfamily i)
  have hw0 : 0 ≤ w0 := hw i false
  have hw1 : 0 ≤ w1 := hw i true
  have hMMnn := wdpairs'_nonneg hw i (𝒜.memberSubfamily i) (ℬ.memberSubfamily i)
  rw [hrec, hA, hB]
  nlinarith [hNN, hMN, hNM, hMM, hMMnn, mul_nonneg hw0 hw0, mul_nonneg hw1 hw0,
    mul_nonneg hw0 hw1, mul_nonneg hw1 hw1]

end Weighted


































def ReimerButterflyMono (n : ℕ) : Prop := ReimerSliceStep n






theorem reimer_wprobCore_of_butterflyMono (h : ∀ n, ReimerButterflyMono n) : ReimerWprobCore :=
  reimer_wprobCore_of_sliceStep h







theorem reimerButterflyMono_of_increasing (n : ℕ) (ψ : Fin n → Bool → ℝ)
    (hψ0 : ∀ i b, 0 ≤ ψ i b) (hψ1 : ∀ i, ψ i false + ψ i true = 1)
    (A B : Set (ConfigSpace (Fin (n + 1)))) (hA : IsIncreasing A) (hB : IsIncreasing B) :
    wprob ψ (disjointOccurrence (slice A false) (slice B false))
        ≤ wprob ψ (disjointOccurrence (slice A false) (slice B true)
                    ∩ disjointOccurrence (slice A true) (slice B false))
    ∧ wprob ψ (disjointOccurrence (slice A false) (slice B true)
                ∪ disjointOccurrence (slice A true) (slice B false))
        ≤ wprob ψ (slice A true) * wprob ψ (slice B true) :=
  reimerSliceStep_holds_on_increasing n ψ hψ0 hψ1 A B hA hB




theorem reimerButterflyMono_satisfiable (n : ℕ) (ψ : Fin n → Bool → ℝ)
    (hψ0 : ∀ i b, 0 ≤ ψ i b) (hψ1 : ∀ i, ψ i false + ψ i true = 1) :
    wprob ψ (disjointOccurrence (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) false)
              (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) false))
        ≤ wprob ψ (disjointOccurrence (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) false)
                    (slice Set.univ true)
                    ∩ disjointOccurrence (slice Set.univ true) (slice Set.univ false))
    ∧ wprob ψ (disjointOccurrence (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) false)
                (slice Set.univ true)
                ∪ disjointOccurrence (slice Set.univ true) (slice Set.univ false))
        ≤ wprob ψ (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) true)
            * wprob ψ (slice Set.univ true) :=
  reimerSliceStep_satisfiable n ψ hψ0 hψ1







































end StatMech

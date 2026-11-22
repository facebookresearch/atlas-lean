/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic

@[expose] public section

namespace MetaMathlibExt

open Finset

private def partner (n : ℕ) (j : Fin n) : Fin n :=
  if _h : j.val % 2 = 0 then
    if _h2 : j.val + 1 < n then ⟨j.val + 1, _h2⟩ else j
  else ⟨j.val - 1, by have hj := j.isLt; omega⟩

private lemma partner_val (n : ℕ) (j : Fin n) :
    (partner n j).val =
      if j.val % 2 = 0 then (if j.val + 1 < n then j.val + 1 else j.val)
      else j.val - 1 := by
  unfold partner
  by_cases he : j.val % 2 = 0 <;> simp only [he, dite_true, dite_false]
  · by_cases h2 : j.val + 1 < n <;> simp only [h2, dite_true, dite_false]
    · rfl
    · rfl
  · rfl

private lemma partner_block (n : ℕ) (j : Fin n) : (partner n j).val / 2 = j.val / 2 := by
  have h := partner_val n j
  by_cases he : j.val % 2 = 0
  · rw [h]
    simp only [he, ite_true]
    by_cases h2 : j.val + 1 < n
    · simp only [h2, ite_true]; omega
    · simp only [h2, ite_false]
  · rw [h]
    simp only [he, ite_false]
    have hodd : j.val % 2 = 1 := by omega
    omega

private lemma partner_invol (n : ℕ) (j : Fin n) : partner n (partner n j) = j := by
  apply Fin.ext
  have h1 := partner_val n (partner n j)
  change (partner n (partner n j)).val = j.val
  by_cases he : j.val % 2 = 0
  · by_cases h2 : j.val + 1 < n
    · have hval : (partner n j).val = j.val + 1 := by
        have h := partner_val n j
        rw [h]
        simp only [he, ite_true, h2, ite_true]
      rw [hval] at h1
      have hne : ¬ (j.val + 1) % 2 = 0 := by omega
      rw [h1]
      simp only [hne, ite_false]
      omega
    · have hval : (partner n j).val = j.val := by
        have h := partner_val n j
        rw [h]
        simp only [he, ite_true, h2, ite_false]
      rw [hval] at h1
      rw [h1]
      simp only [he, ite_true, h2, ite_false]
  · have hval : (partner n j).val = j.val - 1 := by
      have h := partner_val n j
      rw [h]
      simp only [he, ite_false]
    rw [hval] at h1
    have hodd : j.val % 2 = 1 := by omega
    have heven : (j.val - 1) % 2 = 0 := by omega
    have h2' : j.val - 1 + 1 < n := by have hj := j.isLt; omega
    rw [h1]
    simp only [heven, ite_true, h2', ite_true]
    omega

private lemma partner_succ (n : ℕ) (j : Fin n) (he : j.val % 2 = 0) (h2 : j.val + 1 < n) :
    (partner n j).val = j.val + 1 := by
  rw [partner_val]
  simp only [he, ite_true, h2, ite_true]

private def bstart (n : ℕ) (j : Fin n) : Fin n :=
  if _h : j.val % 2 = 0 then j else ⟨j.val - 1, by have hj := j.isLt; omega⟩

private lemma bstart_val (n : ℕ) (j : Fin n) :
    (bstart n j).val = if j.val % 2 = 0 then j.val else j.val - 1 := by
  unfold bstart
  by_cases he : j.val % 2 = 0 <;> simp only [he, dite_true, dite_false]
  · rfl
  · rfl

private lemma bstart_block (n : ℕ) (j : Fin n) : (bstart n j).val / 2 = j.val / 2 := by
  rw [bstart_val]
  by_cases he : j.val % 2 = 0
  · simp only [he, ite_true]
  · simp only [he, ite_false]
    have hodd : j.val % 2 = 1 := by omega
    omega

private lemma bstart_of_even (n : ℕ) (j : Fin n) (he : j.val % 2 = 0) :
    bstart n j = j := by
  apply Fin.ext
  rw [bstart_val]
  simp only [he, ite_true]

private lemma bstart_partner (n : ℕ) (j : Fin n) : bstart n (partner n j) = bstart n j := by
  apply Fin.ext
  rw [bstart_val, bstart_val]
  have hp := partner_val n j
  by_cases he : j.val % 2 = 0
  · by_cases h2 : j.val + 1 < n
    · have hval : (partner n j).val = j.val + 1 := by
        rw [hp]; simp only [he, ite_true, h2, ite_true]
      have hne : ¬ (j.val + 1) % 2 = 0 := by omega
      have arith : j.val + 1 - 1 = j.val := by omega
      rw [hval]
      simp only [hne, ite_false, he, ite_true, arith]
    · have hval : (partner n j).val = j.val := by
        rw [hp]; simp only [he, ite_true, h2, ite_false]
      rw [hval]
  · have hval : (partner n j).val = j.val - 1 := by
      rw [hp]; simp only [he, ite_false]
    have hodd : j.val % 2 = 1 := by omega
    have heven : (j.val - 1) % 2 = 0 := by omega
    rw [hval]
    simp only [heven, ite_true, he, ite_false]

private lemma bstart_eq_of_block_eq (n : ℕ) (a b : Fin n) (h : a.val / 2 = b.val / 2) :
    bstart n a = bstart n b := by
  apply Fin.ext
  rw [bstart_val, bstart_val]
  by_cases hea : a.val % 2 = 0 <;> by_cases heb : b.val % 2 = 0
  · simp only [hea, heb, ite_true]; omega
  · simp only [hea, heb, ite_true, ite_false]; omega
  · simp only [hea, heb, ite_false, ite_true]; omega
  · simp only [hea, heb, ite_false]; omega

private def sigmaPos (n : ℕ) (T : Finset (Fin n)) (j : Fin n) : Fin n :=
  if bstart n j ∈ T then partner n j else j

private lemma sigmaPos_is (n : ℕ) (T : Finset (Fin n)) (j : Fin n)
    (h : bstart n j ∈ T) : sigmaPos n T j = partner n j := by
  unfold sigmaPos
  simp only [h, ite_true]

private lemma sigmaPos_isnot (n : ℕ) (T : Finset (Fin n)) (j : Fin n)
    (h : bstart n j ∉ T) : sigmaPos n T j = j := by
  unfold sigmaPos
  simp only [h, ite_false]

private lemma sigma_invol (n : ℕ) (T : Finset (Fin n)) (j : Fin n) :
    sigmaPos n T (sigmaPos n T j) = j := by
  by_cases h : bstart n j ∈ T
  · have e1 : sigmaPos n T j = partner n j := sigmaPos_is n T j h
    have hc : bstart n (sigmaPos n T j) ∈ T := by
      rw [e1, bstart_partner]; exact h
    have hc' : bstart n (partner n j) ∈ T := by
      rw [← e1]; exact hc
    have e2 : sigmaPos n T (sigmaPos n T j) = partner n (partner n j) := by
      rw [e1]; exact sigmaPos_is n T _ hc'
    rw [e2, partner_invol]
  · have e1 : sigmaPos n T j = j := sigmaPos_isnot n T j h
    rw [e1]; exact e1

private lemma sigma_block (n : ℕ) (T : Finset (Fin n)) (j : Fin n) :
    (sigmaPos n T j).val / 2 = j.val / 2 := by
  by_cases h : bstart n j ∈ T
  · rw [sigmaPos_is n T j h]; exact partner_block n j
  · rw [sigmaPos_isnot n T j h]

private lemma cross_iff (n : ℕ) (a b : Fin n) (h : a.val / 2 ≠ b.val / 2) :
    (a.val < b.val ↔ a.val / 2 < b.val / 2) := by
  constructor <;> intro hi <;> omega

private lemma sigma_cross (n : ℕ) (T : Finset (Fin n)) (a b : Fin n)
    (h : a.val / 2 ≠ b.val / 2) :
    ((sigmaPos n T a).val < (sigmaPos n T b).val ↔ a.val < b.val) := by
  have ha := sigma_block n T a
  have hb := sigma_block n T b
  have hne : (sigmaPos n T a).val / 2 ≠ (sigmaPos n T b).val / 2 := by omega
  rw [cross_iff n _ _ hne, cross_iff n _ _ h, ha, hb]

private def psb (n : ℕ) (w : Fin n → Fin 2) : Bool :=
  decide (∀ j j' : Fin n, j.val % 2 = 0 → j'.val = j.val + 1 → w j ≤ w j')

private def ascSet (n : ℕ) (w : Fin n → Fin 2) : Finset (Fin n) :=
  Finset.univ.filter
    (fun j => j.val % 2 = 0 ∧ ∃ j' : Fin n, j'.val = j.val + 1 ∧ w j < w j')

private def descSet (n : ℕ) (w : Fin n → Fin 2) : Finset (Fin n) :=
  Finset.univ.filter
    (fun j => j.val % 2 = 0 ∧ ∃ j' : Fin n, j'.val = j.val + 1 ∧ w j' < w j)

private def invSet (n : ℕ) (w : Fin n → Fin 2) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2 ∧ w p.1 > w p.2)

private def wordsSet (n k : ℕ) : Finset (Fin n → Fin 2) :=
  Finset.univ.filter
    (fun v => (Finset.univ.filter (fun i : Fin n => v i = (1 : Fin 2))).card = k)

private def flip (n : ℕ) (T : Finset (Fin n)) (w : Fin n → Fin 2) : Fin n → Fin 2 :=
  fun i => w (sigmaPos n T i)

private def newSet (n : ℕ) (T : Finset (Fin n)) (w : Fin n → Fin 2) :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter
    (fun p => sigmaPos n T p.1 < sigmaPos n T p.2 ∧ w p.1 > w p.2)

private def extraSet (n : ℕ) (T : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  T.image (fun j => (partner n j, j))

private lemma mem_asc (n : ℕ) (w : Fin n → Fin 2) (j : Fin n) :
    j ∈ ascSet n w ↔
      j.val % 2 = 0 ∧ j.val + 1 < n ∧ w j < w (partner n j) := by
  unfold ascSet
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨he, j', hj', hlt⟩
    have h2 : j.val + 1 < n := by have hj := j'.isLt; omega
    have hpeq : j' = partner n j := by
      apply Fin.ext
      have hps := partner_succ n j he h2
      omega
    refine ⟨he, h2, ?_⟩
    rw [← hpeq]; exact hlt
  · rintro ⟨he, h2, hlt⟩
    exact ⟨he, partner n j, partner_succ n j he h2, hlt⟩

private lemma mem_desc (n : ℕ) (w : Fin n → Fin 2) (j : Fin n) :
    j ∈ descSet n w ↔
      j.val % 2 = 0 ∧ j.val + 1 < n ∧ w (partner n j) < w j := by
  unfold descSet
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨he, j', hj', hlt⟩
    have h2 : j.val + 1 < n := by have hj := j'.isLt; omega
    have hpeq : j' = partner n j := by
      apply Fin.ext
      have hps := partner_succ n j he h2
      omega
    refine ⟨he, h2, ?_⟩
    rw [← hpeq]; exact hlt
  · rintro ⟨he, h2, hlt⟩
    exact ⟨he, partner n j, partner_succ n j he h2, hlt⟩

private lemma fin2_of_lt (a b : Fin 2) (h : a < b) : a = 0 ∧ b = 1 := by
  have hlt : a.val < b.val := h
  have hai := a.isLt
  have hbi := b.isLt
  have ha : a.val = 0 := by omega
  have hb : b.val = 1 := by omega
  constructor
  · apply Fin.ext
    show a.val = (0 : Fin 2).val
    rw [ha]; rfl
  · apply Fin.ext
    show b.val = (1 : Fin 2).val
    rw [hb]; rfl

private lemma ps_empty_desc (n : ℕ) (w : Fin n → Fin 2) (h : psb n w = true) :
    descSet n w = ∅ := by
  have hall := of_decide_eq_true h
  rw [Finset.eq_empty_iff_forall_notMem]
  intro j hj
  rw [mem_desc] at hj
  obtain ⟨he, h2, hlt⟩ := hj
  have hle := hall j (partner n j) he (partner_succ n j he h2)
  exact absurd hlt (not_lt_of_ge hle)

-- Step A: reindex inversion set of flipped word by sigma x sigma
private lemma card_reindex (n : ℕ) (T : Finset (Fin n)) (w : Fin n → Fin 2) :
    (invSet n (flip n T w)).card = (newSet n T w).card := by
  apply Finset.card_bij'
    (fun p _ => (sigmaPos n T p.1, sigmaPos n T p.2))
    (fun p _ => (sigmaPos n T p.1, sigmaPos n T p.2))
  · intro p hp
    simp only [invSet, newSet, mem_filter, mem_univ, true_and] at hp ⊢
    obtain ⟨hlt, hgt⟩ := hp
    have g2 : w (sigmaPos n T p.1) > w (sigmaPos n T p.2) := hgt
    have e1 := sigma_invol n T p.1
    have e2 := sigma_invol n T p.2
    change sigmaPos n T (sigmaPos n T p.1) < sigmaPos n T (sigmaPos n T p.2) ∧
      w (sigmaPos n T p.1) > w (sigmaPos n T p.2)
    rw [e1, e2]
    exact ⟨hlt, g2⟩
  · intro p hp
    simp only [invSet, newSet, mem_filter, mem_univ, true_and] at hp ⊢
    obtain ⟨hlt, hgt⟩ := hp
    have g2 : flip n T w (sigmaPos n T p.1) > flip n T w (sigmaPos n T p.2) := by
      change w (sigmaPos n T (sigmaPos n T p.1)) > w (sigmaPos n T (sigmaPos n T p.2))
      rw [sigma_invol n T p.1, sigma_invol n T p.2]
      exact hgt
    exact ⟨hlt, g2⟩
  · intro p hp
    change (sigmaPos n T (sigmaPos n T p.1), sigmaPos n T (sigmaPos n T p.2)) = p
    rw [sigma_invol n T p.1, sigma_invol n T p.2]
  · intro p hp
    change (sigmaPos n T (sigmaPos n T p.1), sigmaPos n T (sigmaPos n T p.2)) = p
    rw [sigma_invol n T p.1, sigma_invol n T p.2]

private lemma ones_flip (n : ℕ) (T : Finset (Fin n)) (w : Fin n → Fin 2) :
    (Finset.univ.filter (fun i => w (sigmaPos n T i) = (1 : Fin 2))).card =
      (Finset.univ.filter (fun i => w i = (1 : Fin 2))).card := by
  apply Finset.card_bij' (fun i _ => sigmaPos n T i) (fun i _ => sigmaPos n T i)
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    exact ha
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    rw [sigma_invol]; exact hb
  · intro a ha
    exact sigma_invol n T a
  · intro a ha
    exact sigma_invol n T a

private lemma flip_mem_words (n k : ℕ) (T : Finset (Fin n)) (w : Fin n → Fin 2)
    (hw : w ∈ wordsSet n k) : flip n T w ∈ wordsSet n k := by
  simp only [wordsSet, mem_filter, mem_univ, true_and] at hw ⊢
  have ho := ones_flip n T w
  change (Finset.univ.filter (fun i => flip n T w i = (1 : Fin 2))).card = k
  have heq : Finset.univ.filter (fun i => flip n T w i = (1 : Fin 2)) =
      Finset.univ.filter (fun i => w (sigmaPos n T i) = (1 : Fin 2)) := rfl
  rw [heq, ho]; exact hw

-- Step B: the reindexed set is the disjoint union of old inversions and new pairs
private lemma extra_card (n : ℕ) (T : Finset (Fin n)) :
    (extraSet n T).card = T.card := by
  unfold extraSet
  apply Finset.card_image_of_injective
  intro a b hab
  simp only [Prod.mk.injEq] at hab
  exact hab.2

private lemma extra_sub_new (n : ℕ) (T : Finset (Fin n)) (w : Fin n → Fin 2)
    (hT : T ⊆ ascSet n w) : extraSet n T ⊆ newSet n T w := by
  intro q hq
  simp only [extraSet, mem_image] at hq
  obtain ⟨j, hjT, hjq⟩ := hq
  have hA := (mem_asc n w j).mp (hT hjT)
  obtain ⟨he, h2, hlt⟩ := hA
  have hBj : bstart n j = j := bstart_of_even n j he
  have hmem : bstart n j ∈ T := by rw [hBj]; exact hjT
  have hSj : sigmaPos n T j = partner n j := sigmaPos_is n T j hmem
  have hSp : sigmaPos n T (partner n j) = j := by
    have hmem2 : bstart n (partner n j) ∈ T := by
      rw [bstart_partner, hBj]; exact hjT
    calc sigmaPos n T (partner n j) = partner n (partner n j) :=
            sigmaPos_is n T _ hmem2
      _ = j := partner_invol n j
  have hq1 : q.1 = partner n j := (congrArg Prod.fst hjq).symm
  have hq2 : q.2 = j := (congrArg Prod.snd hjq).symm
  simp only [newSet, mem_filter, mem_univ, true_and]
  rw [hq1, hq2, hSp, hSj]
  constructor
  · rw [Fin.lt_def, partner_succ n j he h2]; omega
  · exact hlt

private lemma old_sub_new (n : ℕ) (T : Finset (Fin n)) (w : Fin n → Fin 2)
    (hps : psb n w = true) (hT : T ⊆ ascSet n w) :
    invSet n w ⊆ newSet n T w := by
  have hall := of_decide_eq_true hps
  intro p hp
  simp only [invSet, newSet, mem_filter, mem_univ, true_and] at hp ⊢
  obtain ⟨hlt, hgt⟩ := hp
  refine ⟨?_, hgt⟩
  by_cases hblk : p.1.val / 2 ≠ p.2.val / 2
  · exact Fin.lt_def.mpr ((sigma_cross n T p.1 p.2 hblk).mpr (Fin.lt_def.mp hlt))
  · rw [not_ne_iff] at hblk
    by_cases hmem : bstart n p.1 ∈ T
    · have hea : p.1.val % 2 = 0 := by
        have ha_lt := p.1.isLt
        have hb_lt := p.2.isLt
        have hltV : p.1.val < p.2.val := Fin.lt_def.mp hlt
        omega
      have haE : p.1 = bstart n p.1 := (bstart_of_even n p.1 hea).symm
      have hmemA : p.1 ∈ T := by rw [haE]; exact hmem
      have hA := (mem_asc n w p.1).mp (hT hmemA)
      obtain ⟨he2, h2, hasc⟩ := hA
      have hbP : p.2 = partner n p.1 := by
        apply Fin.ext
        have hps2 := partner_succ n p.1 he2 h2
        have ha_lt := p.1.isLt
        have hb_lt := p.2.isLt
        have hltV : p.1.val < p.2.val := Fin.lt_def.mp hlt
        omega
      rw [hbP] at hgt
      exact absurd hgt (not_lt_of_ge (le_of_lt hasc))
    · have hbb : bstart n p.2 = bstart n p.1 :=
        bstart_eq_of_block_eq n p.2 p.1 hblk.symm
      have e1 : sigmaPos n T p.1 = p.1 := sigmaPos_isnot n T p.1 hmem
      have e2 : sigmaPos n T p.2 = p.2 :=
        sigmaPos_isnot n T p.2 (by rw [hbb]; exact hmem)
      rw [e1, e2]; exact hlt

private lemma new_sub_union (n : ℕ) (T : Finset (Fin n)) (w : Fin n → Fin 2)
    (hT : T ⊆ ascSet n w) : newSet n T w ⊆ invSet n w ∪ extraSet n T := by
  intro p hp
  simp only [newSet, mem_filter, mem_univ, true_and] at hp
  obtain ⟨hsig, hgt⟩ := hp
  simp only [mem_union, invSet, extraSet, mem_filter, mem_univ, true_and,
    mem_image]
  by_cases hblk : p.1.val / 2 ≠ p.2.val / 2
  · left
    have hltV : p.1.val < p.2.val :=
      (sigma_cross n T p.1 p.2 hblk).mp (Fin.lt_def.mp hsig)
    exact ⟨Fin.lt_def.mpr hltV, hgt⟩
  · rw [not_ne_iff] at hblk
    by_cases hmem : bstart n p.1 ∈ T
    · have hA := (mem_asc n w (bstart n p.1)).mp (hT hmem)
      obtain ⟨he_even, he_succ, he_asc⟩ := hA
      have hbA := bstart_block n p.1
      have hbB : (bstart n p.1).val / 2 = p.2.val / 2 := by omega
      have ha_lt := p.1.isLt
      have hb_lt := p.2.isLt
      have he_lt := (bstart n p.1).isLt
      have ha_cases : p.1.val = (bstart n p.1).val ∨
          p.1.val = (bstart n p.1).val + 1 := by omega
      have hb_cases : p.2.val = (bstart n p.1).val ∨
          p.2.val = (bstart n p.1).val + 1 := by omega
      have hne : p.1 ≠ p.2 := by
        intro hab
        rw [hab] at hgt
        exact lt_irrefl _ hgt
      have hneV : p.1.val ≠ p.2.val := fun h => hne (Fin.ext h)
      rcases ha_cases with haV | haV <;> rcases hb_cases with hbV | hbV
      · exact absurd (by omega : p.1.val = p.2.val) hneV
      · left
        have hltV : p.1.val < p.2.val := by omega
        exact ⟨Fin.lt_def.mpr hltV, hgt⟩
      · right
        have haP : p.1 = partner n (bstart n p.1) := by
          apply Fin.ext
          have hps2 := partner_succ n (bstart n p.1) he_even he_succ
          omega
        have hbE : p.2 = bstart n p.1 := by
          apply Fin.ext
          omega
        exact ⟨bstart n p.1, hmem, Prod.ext haP.symm hbE.symm⟩
      · exact absurd (by omega : p.1.val = p.2.val) hneV
    · left
      have hbb : bstart n p.2 = bstart n p.1 :=
        bstart_eq_of_block_eq n p.2 p.1 hblk.symm
      have e1 : sigmaPos n T p.1 = p.1 := sigmaPos_isnot n T p.1 hmem
      have e2 : sigmaPos n T p.2 = p.2 :=
        sigmaPos_isnot n T p.2 (by rw [hbb]; exact hmem)
      have hlt : p.1 < p.2 := by rw [← e1, ← e2]; exact hsig
      exact ⟨hlt, hgt⟩

private lemma disjoint_old_extra (n : ℕ) (T : Finset (Fin n)) (w : Fin n → Fin 2)
    (hT : T ⊆ ascSet n w) : Disjoint (invSet n w) (extraSet n T) := by
  rw [Finset.disjoint_left]
  intro q hq_old hq_ex
  simp only [extraSet, mem_image] at hq_ex
  obtain ⟨j, hjT, hjq⟩ := hq_ex
  have hA := (mem_asc n w j).mp (hT hjT)
  obtain ⟨he, h2, hlt⟩ := hA
  have hq1 : q.1 = partner n j := (congrArg Prod.fst hjq).symm
  have hq2 : q.2 = j := (congrArg Prod.snd hjq).symm
  simp only [invSet, mem_filter, mem_univ, true_and] at hq_old
  obtain ⟨hlt2, _⟩ := hq_old
  rw [hq1, hq2, Fin.lt_def, partner_succ n j he h2] at hlt2
  omega

private lemma new_eq_union (n : ℕ) (T : Finset (Fin n)) (w : Fin n → Fin 2)
    (hps : psb n w = true) (hT : T ⊆ ascSet n w) :
    newSet n T w = invSet n w ∪ extraSet n T := by
  apply Finset.Subset.antisymm
  · exact new_sub_union n T w hT
  · apply Finset.union_subset
    · exact old_sub_new n T w hps hT
    · exact extra_sub_new n T w hT

private lemma weight_key (n : ℕ) (T : Finset (Fin n)) (w : Fin n → Fin 2)
    (hps : psb n w = true) (hT : T ⊆ ascSet n w) :
    (invSet n (flip n T w)).card = (invSet n w).card + T.card := by
  rw [card_reindex n T w, new_eq_union n T w hps hT,
    Finset.card_union_of_disjoint (disjoint_old_extra n T w hT),
    extra_card n T]

private lemma flip_ps (n : ℕ) (v : Fin n → Fin 2) :
    psb n (flip n (descSet n v) v) = true := by
  unfold psb
  apply decide_eq_true
  intro j j' he hj'
  have h2 : j.val + 1 < n := by have hjj := j'.isLt; omega
  have hjP : j' = partner n j := by
    apply Fin.ext
    have hps := partner_succ n j he h2
    omega
  have hBj : bstart n j = j := bstart_of_even n j he
  change v (sigmaPos n (descSet n v) j) ≤ v (sigmaPos n (descSet n v) j')
  by_cases hmem : bstart n j ∈ descSet n v
  · have e1 : sigmaPos n (descSet n v) j = partner n j :=
      sigmaPos_is n _ j hmem
    have hmem2 : bstart n (partner n j) ∈ descSet n v := by
      rw [bstart_partner]; exact hmem
    have e2 : sigmaPos n (descSet n v) (partner n j) = j := by
      calc sigmaPos n (descSet n v) (partner n j)
          = partner n (partner n j) := sigmaPos_is n _ _ hmem2
        _ = j := partner_invol n j
    have hD' : v (partner n j) < v j := by
      have hjD : j ∈ descSet n v := by rw [← hBj]; exact hmem
      exact ((mem_desc n v j).mp hjD).2.2
    rw [e1, hjP, e2]
    exact le_of_lt hD'
  · have e1 : sigmaPos n (descSet n v) j = j :=
      sigmaPos_isnot n _ j hmem
    have e2 : sigmaPos n (descSet n v) j' = j' := by
      apply sigmaPos_isnot
      rw [hjP, bstart_partner]; exact hmem
    rw [e1, e2]
    by_contra hcon
    have hlt : v j' < v j := lt_of_not_ge hcon
    have hjD : j ∈ descSet n v :=
      (mem_desc n v j).mpr ⟨he, h2, by rw [← hjP]; exact hlt⟩
    have hjD' : bstart n j ∈ descSet n v := by rw [hBj]; exact hjD
    exact hmem hjD'

private lemma desc_sub_asc_flip (n : ℕ) (v : Fin n → Fin 2) :
    descSet n v ⊆ ascSet n (flip n (descSet n v) v) := by
  intro j hj
  have hA := (mem_desc n v j).mp hj
  obtain ⟨he, h2, hlt⟩ := hA
  have hBj : bstart n j = j := bstart_of_even n j he
  have hmem : bstart n j ∈ descSet n v := by rw [hBj]; exact hj
  have e1 : sigmaPos n (descSet n v) j = partner n j :=
    sigmaPos_is n _ j hmem
  have e2 : sigmaPos n (descSet n v) (partner n j) = j := by
    have hmem2 : bstart n (partner n j) ∈ descSet n v := by
      rw [bstart_partner, hBj]; exact hj
    calc sigmaPos n (descSet n v) (partner n j)
        = partner n (partner n j) := sigmaPos_is n _ _ hmem2
      _ = j := partner_invol n j
  rw [mem_asc]
  refine ⟨he, h2, ?_⟩
  change v (sigmaPos n (descSet n v) j) < v (sigmaPos n (descSet n v) (partner n j))
  rw [e1, e2]; exact hlt

private lemma fwd_desc_eq (n : ℕ) (w : Fin n → Fin 2) (T : Finset (Fin n))
    (hps : psb n w = true) (hT : T ⊆ ascSet n w) :
    descSet n (flip n T w) = T := by
  apply Finset.Subset.antisymm
  · intro j hj
    have hA := (mem_desc n (flip n T w) j).mp hj
    obtain ⟨he, h2, hlt⟩ := hA
    have hBj : bstart n j = j := bstart_of_even n j he
    by_cases hmem : bstart n j ∈ T
    · rw [hBj] at hmem; exact hmem
    · have e1 : sigmaPos n T j = j := sigmaPos_isnot n T j hmem
      have e2 : sigmaPos n T (partner n j) = partner n j := by
        apply sigmaPos_isnot
        rw [bstart_partner]; exact hmem
      have hlt2 : w (sigmaPos n T (partner n j)) < w (sigmaPos n T j) := hlt
      rw [e2, e1] at hlt2
      have hjD : j ∈ descSet n w :=
        (mem_desc n w j).mpr ⟨he, h2, hlt2⟩
      have hempty := ps_empty_desc n w hps
      simp [hempty] at hjD
  · intro j hjT
    have hA := (mem_asc n w j).mp (hT hjT)
    obtain ⟨he, h2, hasc⟩ := hA
    have hBj : bstart n j = j := bstart_of_even n j he
    have hmem : bstart n j ∈ T := by rw [hBj]; exact hjT
    have e1 : sigmaPos n T j = partner n j := sigmaPos_is n T j hmem
    have e2 : sigmaPos n T (partner n j) = j := by
      have hmem2 : bstart n (partner n j) ∈ T := by
        rw [bstart_partner, hBj]; exact hjT
      calc sigmaPos n T (partner n j) = partner n (partner n j) :=
              sigmaPos_is n T _ hmem2
        _ = j := partner_invol n j
    rw [mem_desc]
    refine ⟨he, h2, ?_⟩
    have goal2 : w (sigmaPos n T (partner n j)) < w (sigmaPos n T j) := by
      rw [e2, e1]; exact hasc
    exact goal2

private lemma flip_flip (n : ℕ) (T : Finset (Fin n)) (w : Fin n → Fin 2) :
    flip n T (flip n T w) = w := by
  funext i
  change w (sigmaPos n T (sigmaPos n T i)) = w i
  rw [sigma_invol]

private lemma expand_one_add {α : Type*} (s : Finset α) :
    ((1 : Polynomial ℕ) + Polynomial.X) ^ s.card =
      ∑ t ∈ s.powerset, (Polynomial.X : Polynomial ℕ) ^ t.card := by
  classical
  have h := Finset.prod_add (fun _ : α => (Polynomial.X : Polynomial ℕ))
    (fun _ : α => (1 : Polynomial ℕ)) s
  have hLHS : ∏ i ∈ s, ((fun _ : α => (Polynomial.X : Polynomial ℕ)) i +
      (fun _ : α => (1 : Polynomial ℕ)) i)
      = ((1 : Polynomial ℕ) + Polynomial.X) ^ s.card := by
    have hterm : ∀ i ∈ s, ((fun _ : α => (Polynomial.X : Polynomial ℕ)) i +
        (fun _ : α => (1 : Polynomial ℕ)) i)
        = ((1 : Polynomial ℕ) + Polynomial.X) := by
      intro i _
      simp [add_comm]
    rw [Finset.prod_congr rfl hterm, Finset.prod_const]
  rw [← hLHS, h]
  apply Finset.sum_congr rfl
  intro t ht
  simp [Finset.prod_const, Finset.prod_const_one]

private theorem gaussian_pair_sorted_expansion_test (n k : ℕ) :
    Finset.sum (wordsSet n k)
        (fun v => (Polynomial.X : Polynomial ℕ) ^ (invSet n v).card) =
      Finset.sum ((wordsSet n k).filter (fun v => psb n v = true))
        (fun v => (Polynomial.X : Polynomial ℕ) ^ (invSet n v).card *
          ((1 : Polynomial ℕ) + Polynomial.X) ^ (ascSet n v).card) := by
  have expand_w : ∀ w ∈ (wordsSet n k).filter (fun v => psb n v = true),
      (Polynomial.X : Polynomial ℕ) ^ (invSet n w).card *
        ((1 : Polynomial ℕ) + Polynomial.X) ^ (ascSet n w).card
      = ∑ T ∈ (ascSet n w).powerset,
          (Polynomial.X : Polynomial ℕ) ^ ((invSet n w).card + T.card) := by
    intro w hw
    rw [expand_one_add (ascSet n w), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    rw [pow_add]
  have hSigma : (∑ w ∈ (wordsSet n k).filter (fun v => psb n v = true),
          ∑ T ∈ (ascSet n w).powerset,
            (Polynomial.X : Polynomial ℕ) ^ ((invSet n w).card + T.card))
      = ∑ x ∈ ((wordsSet n k).filter (fun v => psb n v = true)).sigma
          (fun w => (ascSet n w).powerset),
          (Polynomial.X : Polynomial ℕ) ^ ((invSet n x.1).card + x.2.card) :=
    Finset.sum_sigma' _ _ _
  have hBij : (∑ x ∈ ((wordsSet n k).filter (fun v => psb n v = true)).sigma
          (fun w => (ascSet n w).powerset),
          (Polynomial.X : Polynomial ℕ) ^ ((invSet n x.1).card + x.2.card))
      = ∑ v ∈ wordsSet n k,
          (Polynomial.X : Polynomial ℕ) ^ (invSet n v).card := by
    refine Finset.sum_bij'
      (s := ((wordsSet n k).filter (fun v => psb n v = true)).sigma
        (fun w => (ascSet n w).powerset))
      (t := wordsSet n k)
      (f := fun x => (Polynomial.X : Polynomial ℕ) ^
        ((invSet n x.1).card + x.2.card))
      (g := fun v => (Polynomial.X : Polynomial ℕ) ^ (invSet n v).card)
      (fun x _ => flip n x.2 x.1)
      (fun v _ => Sigma.mk (flip n (descSet n v) v) (descSet n v))
      ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_sigma] at hx
      obtain ⟨hx1, hx2⟩ := hx
      exact flip_mem_words n k x.2 x.1 (Finset.mem_of_mem_filter x.1 hx1)
    · intro v hv
      rw [Finset.mem_sigma]
      constructor
      · rw [Finset.mem_filter]
        exact ⟨flip_mem_words n k (descSet n v) v hv, flip_ps n v⟩
      · rw [Finset.mem_powerset]
        exact desc_sub_asc_flip n v
    · intro x hx
      rw [Finset.mem_sigma] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have hps : psb n x.1 = true := (Finset.mem_filter.mp hx1).2
      have hsub : x.2 ⊆ ascSet n x.1 := Finset.mem_powerset.mp hx2
      have hD : descSet n (flip n x.2 x.1) = x.2 :=
        fwd_desc_eq n x.1 x.2 hps hsub
      have hpair : Sigma.mk (flip n (descSet n (flip n x.2 x.1)) (flip n x.2 x.1))
          (descSet n (flip n x.2 x.1)) = x := by
        have hF : flip n x.2 (flip n x.2 x.1) = x.1 := flip_flip n x.2 x.1
        rw [hD, hF]
      exact hpair
    · intro v hv
      exact flip_flip n (descSet n v) v
    · intro x hx
      rw [Finset.mem_sigma] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have hps : psb n x.1 = true := (Finset.mem_filter.mp hx1).2
      have hsub : x.2 ⊆ ascSet n x.1 := Finset.mem_powerset.mp hx2
      have hw := weight_key n x.2 x.1 hps hsub
      rw [hw]
  rw [← hBij, ← hSigma]
  exact Finset.sum_congr rfl (fun w hw => (expand_w w hw).symm)


/--
**Ehrenborg–Readdy expansion of the Gaussian coefficient.** Let $n$ and $k$ be natural numbers
and let $W$ be the set of words $v = v_0 v_1 \cdots v_{n-1}$ over the alphabet $\{0, 1\}$ with
exactly $k$ letters equal to $1$. For a word $v$, let $\operatorname{inv}(v)$ be the number of
pairs $i < j$ with $v_i > v_j$; call $v$ pair-sorted when $v_{2i} \le v_{2i+1}$ for every $i$
with $2i + 1 < n$; and let $\operatorname{asc}_{\mathrm{odd}}(v)$ be the number of $i$ with
$2i + 1 < n$ and $v_{2i} < v_{2i+1}$. Then, in the polynomial ring $\mathbb{N}[q]$,

$$\sum_{v \in W} q^{\operatorname{inv}(v)} = \sum_{v \in W,\ v \text{ pair-sorted}}
q^{\operatorname{inv}(v)} (1 + q)^{\operatorname{asc}_{\mathrm{odd}}(v)}.$$

The left side is MacMahon's inversion generating polynomial of $W$, which equals the Gaussian
coefficient $\binom{n}{k}_q$. Positions are numbered from $0$, so the pairs $(v_{2i}, v_{2i+1})$
are the source's pairs of positions $(1, 2), (3, 4), \ldots$, and
$\operatorname{asc}_{\mathrm{odd}}$ counts its odd ascents.

Proves `Wanted` entry `gaussian_pair_sorted_expansion`.

Source: Richard Ehrenborg and Margaret A. Readdy, "The Gaussian
Coefficient Revisited," Journal of Integer Sequences 19 (2016),
Article 16.7.8, Corollary 3 (label corollary_q_1_q), equation
(equation_smaller_q_binomial), lines 301–311,
https://cs.uwaterloo.ca/journals/JIS/VOL19/Ehrenborg/ehr3.tex
-/
theorem gaussian_pair_sorted_expansion (n k : ℕ) :
  let words : Finset (Fin n → Fin 2) :=
    Finset.univ.filter
      (fun v => (Finset.univ.filter (fun i : Fin n => v i = (1 : Fin 2))).card = k);
  let inv : (Fin n → Fin 2) → ℕ :=
    fun v => (Finset.univ.filter
      (fun p : Fin n × Fin n => p.1 < p.2 ∧ v p.1 > v p.2)).card;
  let pairSorted : (Fin n → Fin 2) → Bool :=
    fun v => decide (∀ j j' : Fin n, j.val % 2 = 0 →
      j'.val = j.val + 1 → v j ≤ v j');
  let ascOdd : (Fin n → Fin 2) → ℕ :=
    fun v => (Finset.univ.filter
      (fun j : Fin n => j.val % 2 = 0 ∧
        ∃ j' : Fin n, j'.val = j.val + 1 ∧ v j < v j')).card;
  Finset.sum words (fun v => (Polynomial.X : Polynomial ℕ) ^ inv v) =
    Finset.sum (words.filter (fun v => pairSorted v = true))
      (fun v => (Polynomial.X : Polynomial ℕ) ^ inv v *
        ((1 : Polynomial ℕ) + Polynomial.X) ^ ascOdd v) := by
  exact gaussian_pair_sorted_expansion_test n k

end MetaMathlibExt

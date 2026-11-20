/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















































































import Code.Inequalities.ReimerEndpointProve
import Code.Inequalities.ReimerButterflyProve

open Finset
open scoped FinsetFamily

namespace StatMech

variable {α : Type*} [Fintype α] [DecidableEq α]











lemma fwt_insert_mul (w : α → Bool → ℝ) {t : Finset α} {a : α} (ha : a ∉ t) :
    fwt w (insert a t) * w a false = fwt w t * w a true := by
  have h1 : fwt w (insert a t) = w a true * fwt' w a t := by
    rw [fwt_of_mem w (Finset.mem_insert_self a t), Finset.erase_insert ha]
  have h2 : fwt w t = w a false * fwt' w a t := fwt_of_notMem w ha
  rw [h1, h2]; ring
















lemma fwt_le_erase {w : α → Bool → ℝ} (hw0 : ∀ x b, 0 ≤ w x b) {a : α}
    (hdom : w a true ≤ w a false) {s : Finset α} (ha : a ∈ s) :
    fwt w s ≤ fwt w (s.erase a) := by
  have heq : fwt w s * w a false = fwt w (s.erase a) * w a true := by
    have := fwt_insert_mul w (a := a) (t := s.erase a) (Finset.notMem_erase a s)
    rwa [Finset.insert_erase ha] at this
  rcases lt_or_eq_of_le (hw0 a false) with hf | hf
  · have : fwt w s * w a false ≤ fwt w (s.erase a) * w a false := by
      rw [heq]; exact mul_le_mul_of_nonneg_left hdom (fwt_nonneg hw0 _)
    exact le_of_mul_le_mul_right this hf
  · have htrue : w a true = 0 := le_antisymm (hf ▸ hdom) (hw0 a true)
    have hfs : fwt w s = 0 := by
      unfold fwt; apply Finset.prod_eq_zero (Finset.mem_univ a)
      rw [decide_eq_true (by simpa using ha), htrue]
    rw [hfs]; exact fwt_nonneg hw0 _



lemma fwt_le_insert {w : α → Bool → ℝ} (hw0 : ∀ x b, 0 ≤ w x b) {a : α}
    (hdom : w a false ≤ w a true) {s : Finset α} (ha : a ∉ s) :
    fwt w s ≤ fwt w (insert a s) := by
  have heq : fwt w (insert a s) * w a false = fwt w s * w a true := fwt_insert_mul w ha
  rcases lt_or_eq_of_le (hw0 a false) with hf | hf
  · have : fwt w s * w a false ≤ fwt w (insert a s) * w a false := by
      rw [heq]; exact mul_le_mul_of_nonneg_left hdom (fwt_nonneg hw0 _)
    exact le_of_mul_le_mul_right this hf
  · have hfs : fwt w s = 0 := by
      unfold fwt; apply Finset.prod_eq_zero (Finset.mem_univ a)
      rw [decide_eq_false (by simpa using ha), ← hf]
    rw [hfs]; exact fwt_nonneg hw0 _











omit [Fintype α] in

lemma mem_of_erase_notMem {a : α} {𝒜 : Finset (Finset α)} {s : Finset α}
    (hs : s ∈ 𝒜) (h : s.erase a ∉ 𝒜) : a ∈ s := by
  by_contra ha
  rw [Finset.erase_eq_of_notMem ha] at h
  exact h hs









theorem fmarg_le_downCompression {w : α → Bool → ℝ} (hw0 : ∀ x b, 0 ≤ w x b) (a : α)
    (hdom : w a true ≤ w a false) (𝒜 : Finset (Finset α)) :
    fmarg w 𝒜 ≤ fmarg w (Down.compression a 𝒜) := by
  set P := 𝒜.filter (fun s => s.erase a ∈ 𝒜) with hP
  set R := 𝒜.filter (fun s => s.erase a ∉ 𝒜) with hR
  set Q := {s ∈ 𝒜.image (fun s => s.erase a) | s ∉ 𝒜} with hQ
  have hsplit : fmarg w 𝒜 = (∑ s ∈ P, fwt w s) + (∑ s ∈ R, fwt w s) := by
    unfold fmarg; rw [hP, hR, Finset.sum_filter_add_sum_filter_not]
  have hcomp : fmarg w (Down.compression a 𝒜)
      = (∑ s ∈ P, fwt w s) + (∑ s ∈ Q, fwt w s) := by
    unfold fmarg; rw [Down.compression, Finset.sum_disjUnion]
  have hQR : (∑ s ∈ Q, fwt w s) = ∑ s ∈ R, fwt w (s.erase a) := by
    rw [hQ]
    have himg : {s ∈ 𝒜.image (fun s => s.erase a) | s ∉ 𝒜} = R.image (fun s => s.erase a) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_image, hR]
      constructor
      · rintro ⟨⟨s, hs, rfl⟩, hu⟩; exact ⟨s, ⟨hs, hu⟩, rfl⟩
      · rintro ⟨s, hs2, rfl⟩; exact ⟨⟨s, hs2.1, rfl⟩, hs2.2⟩
    rw [himg, Finset.sum_image]
    intro s hs t ht heq
    simp only [hR, Finset.mem_coe, Finset.mem_filter] at hs ht
    have has := mem_of_erase_notMem hs.1 hs.2
    have hat := mem_of_erase_notMem ht.1 ht.2
    simp only [] at heq
    rw [← Finset.insert_erase has, ← Finset.insert_erase hat, heq]
  rw [hsplit, hcomp, hQR]
  refine add_le_add (le_refl _) (Finset.sum_le_sum (fun s hs => ?_))
  rw [hR, Finset.mem_filter] at hs
  exact fwt_le_erase hw0 hdom (mem_of_erase_notMem hs.1 hs.2)








omit [Fintype α] in

lemma compress_singleton_empty (a : α) (s : Finset α) :
    UV.compress ({a} : Finset α) ∅ s = if a ∈ s then s else insert a s := by
  unfold UV.compress
  by_cases ha : a ∈ s
  · rw [if_neg, if_pos ha]
    rintro ⟨hdisj, _⟩; rw [Finset.disjoint_singleton_left] at hdisj; exact hdisj ha
  · rw [if_pos, if_neg ha]
    · rw [Finset.sdiff_empty, Finset.sup_eq_union, Finset.union_comm, Finset.insert_eq]
    · exact ⟨by rw [Finset.disjoint_singleton_left]; exact ha, bot_le⟩

omit [Fintype α] in

lemma notMem_of_compress_notMem {a : α} {𝒜 : Finset (Finset α)} {s : Finset α}
    (hs : s ∈ 𝒜) (h : UV.compress ({a} : Finset α) ∅ s ∉ 𝒜) : a ∉ s := by
  intro ha
  rw [compress_singleton_empty, if_pos ha] at h
  exact h hs








theorem fmarg_le_upCompression {w : α → Bool → ℝ} (hw0 : ∀ x b, 0 ≤ w x b) (a : α)
    (hdom : w a false ≤ w a true) (𝒜 : Finset (Finset α)) :
    fmarg w 𝒜 ≤ fmarg w (UV.compression ({a} : Finset α) ∅ 𝒜) := by
  set c := fun s => UV.compress ({a} : Finset α) ∅ s with hc
  set P := 𝒜.filter (fun s => c s ∈ 𝒜) with hP
  set R := 𝒜.filter (fun s => c s ∉ 𝒜) with hR
  set Q := {s ∈ 𝒜.image c | s ∉ 𝒜} with hQ
  have hsplit : fmarg w 𝒜 = (∑ s ∈ P, fwt w s) + (∑ s ∈ R, fwt w s) := by
    unfold fmarg; rw [hP, hR, Finset.sum_filter_add_sum_filter_not]
  have hcomp : fmarg w (UV.compression ({a} : Finset α) ∅ 𝒜)
      = (∑ s ∈ P, fwt w s) + (∑ s ∈ Q, fwt w s) := by
    unfold fmarg; rw [UV.compression, Finset.sum_union UV.compress_disjoint]
  have hQR : (∑ s ∈ Q, fwt w s) = ∑ s ∈ R, fwt w (insert a s) := by
    rw [hQ]
    have himg : {s ∈ 𝒜.image c | s ∉ 𝒜} = R.image c := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_image, hR]
      constructor
      · rintro ⟨⟨s, hs, rfl⟩, hu⟩; exact ⟨s, ⟨hs, hu⟩, rfl⟩
      · rintro ⟨s, hs2, rfl⟩; exact ⟨⟨s, hs2.1, rfl⟩, hs2.2⟩
    rw [himg, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro s hs
      simp only [hR, Finset.mem_filter] at hs
      have has := notMem_of_compress_notMem hs.1 hs.2
      change fwt w (UV.compress ({a} : Finset α) ∅ s) = fwt w (insert a s)
      rw [compress_singleton_empty, if_neg has]
    · intro s hs t ht heq
      simp only [hR, Finset.mem_coe, Finset.mem_filter] at hs ht
      have has := notMem_of_compress_notMem hs.1 hs.2
      have hat := notMem_of_compress_notMem ht.1 ht.2
      simp only [hc, compress_singleton_empty, if_neg has, if_neg hat] at heq
      have hh : (insert a s).erase a = (insert a t).erase a := by rw [heq]
      rwa [Finset.erase_insert has, Finset.erase_insert hat] at hh
  rw [hsplit, hcomp, hQR]
  refine add_le_add (le_refl _) (Finset.sum_le_sum (fun s hs => ?_))
  rw [hR, Finset.mem_filter] at hs
  exact fwt_le_insert hw0 hdom (notMem_of_compress_notMem hs.1 hs.2)










variable {β : Type*} [Fintype β] [DecidableEq β]












theorem fmarg_le_doubleCompress {w : (β ⊕ β) → Bool → ℝ} (hw0 : ∀ x b, 0 ≤ w x b) (i : β)
    (hL : w (Sum.inl i) true ≤ w (Sum.inl i) false)
    (hR : w (Sum.inr i) false ≤ w (Sum.inr i) true)
    (𝒰 : Finset (Finset (β ⊕ β))) :
    fmarg w 𝒰 ≤ fmarg w (doubleCompress i 𝒰) := by
  unfold doubleCompress upRight upComp downLeft
  calc fmarg w 𝒰
      ≤ fmarg w (Down.compression (Sum.inl i) 𝒰) := fmarg_le_downCompression hw0 _ hL 𝒰
    _ ≤ fmarg w (UV.compression ({Sum.inr i} : Finset (β ⊕ β)) ∅
                  (Down.compression (Sum.inl i) 𝒰)) :=
        fmarg_le_upCompression hw0 _ hR _









noncomputable def iterDoubleCompress (is : List β) (𝒰 : Finset (Finset (β ⊕ β))) :
    Finset (Finset (β ⊕ β)) :=
  is.foldr doubleCompress 𝒰

omit [Fintype β] in
@[simp] lemma iterDoubleCompress_nil (𝒰 : Finset (Finset (β ⊕ β))) :
    iterDoubleCompress [] 𝒰 = 𝒰 := rfl

omit [Fintype β] in
@[simp] lemma iterDoubleCompress_cons (i : β) (is : List β) (𝒰 : Finset (Finset (β ⊕ β))) :
    iterDoubleCompress (i :: is) 𝒰 = doubleCompress i (iterDoubleCompress is 𝒰) := rfl

omit [Fintype β] in


theorem iterDoubleCompress_card (is : List β) (𝒰 : Finset (Finset (β ⊕ β))) :
    (iterDoubleCompress is 𝒰).card = 𝒰.card := by
  induction is with
  | nil => rfl
  | cons i is ih => rw [iterDoubleCompress_cons, doubleCompress_card, ih]





theorem fmarg_le_iterDoubleCompress {w : (β ⊕ β) → Bool → ℝ} (hw0 : ∀ x b, 0 ≤ w x b)
    (hL : ∀ i, w (Sum.inl i) true ≤ w (Sum.inl i) false)
    (hR : ∀ i, w (Sum.inr i) false ≤ w (Sum.inr i) true)
    (is : List β) (𝒰 : Finset (Finset (β ⊕ β))) :
    fmarg w 𝒰 ≤ fmarg w (iterDoubleCompress is 𝒰) := by
  induction is with
  | nil => simp
  | cons i is ih =>
      rw [iterDoubleCompress_cons]
      exact ih.trans (fmarg_le_doubleCompress hw0 i (hL i) (hR i) _)











theorem fmarg_le_downCompression_satisfiable (a : α) (𝒜 : Finset (Finset α)) :
    fmarg (fun _ _ => (1 : ℝ)) 𝒜 ≤ fmarg (fun _ _ => (1 : ℝ)) (Down.compression a 𝒜) :=
  fmarg_le_downCompression (fun _ _ => zero_le_one) a (le_refl _) 𝒜






theorem fmarg_le_doubleCompress_symm {w : (β ⊕ β) → Bool → ℝ} (hw0 : ∀ x b, 0 ≤ w x b)
    (hsym : ∀ x, w x false = w x true) (i : β) (𝒰 : Finset (Finset (β ⊕ β))) :
    fmarg w 𝒰 ≤ fmarg w (doubleCompress i 𝒰) :=
  fmarg_le_doubleCompress hw0 i (le_of_eq (hsym _).symm) (le_of_eq (hsym _)) 𝒰






theorem fmarg_doubleCompress_symm_eq {w : (β ⊕ β) → Bool → ℝ}
    (hsym : ∀ x, w x false = w x true) (i : β) (𝒰 : Finset (Finset (β ⊕ β))) :
    fmarg w (doubleCompress i 𝒰) = fmarg w 𝒰 := by
  have hconst : ∀ S : Finset (β ⊕ β), fwt w S = ∏ x, w x true := fwt_symm_eq_const hsym
  calc fmarg w (doubleCompress i 𝒰)
      = (∏ x, w x true) * ((doubleCompress i 𝒰).card : ℝ) := by
        rw [fmarg]; rw [Finset.sum_congr rfl (fun S _ => hconst S), Finset.sum_const,
          nsmul_eq_mul, mul_comm]
    _ = (∏ x, w x true) * (𝒰.card : ℝ) := by rw [doubleCompress_card]
    _ = fmarg w 𝒰 := by
        rw [fmarg]; rw [Finset.sum_congr rfl (fun S _ => hconst S), Finset.sum_const,
          nsmul_eq_mul, mul_comm]













theorem fmarg_boxDoubled_doubleWeight (w : β → Bool → ℝ) (𝒜 ℬ : Finset (Finset β)) :
    fmarg (doubleWeight w) (boxDoubled 𝒜 ℬ) = wdpairs w 𝒜 ℬ :=
  fmarg_boxDoubled w 𝒜 ℬ









theorem wdpairs_le_iterDoubleCompress_of_symm {w : β → Bool → ℝ}
    (hw0 : ∀ x b, 0 ≤ w x b) (hsym : ∀ x, w x false = w x true)
    (is : List β) (𝒜 ℬ : Finset (Finset β)) :
    wdpairs w 𝒜 ℬ
      ≤ fmarg (doubleWeight w) (iterDoubleCompress is (boxDoubled 𝒜 ℬ)) := by
  have hsymD : ∀ x, doubleWeight w x false = doubleWeight w x true := by
    rintro (a | a) <;> simp only [doubleWeight_apply_inl, doubleWeight_apply_inr] <;> exact hsym a
  have hkey := fmarg_le_iterDoubleCompress (doubleWeight_nonneg hw0)
    (fun i => le_of_eq (hsymD (Sum.inl i)).symm)
    (fun i => le_of_eq (hsymD (Sum.inr i))) is (boxDoubled 𝒜 ℬ)
  rwa [fmarg_boxDoubled_doubleWeight] at hkey








theorem wdpairs_le_mul_of_symm {w : β → Bool → ℝ}
    (hw0 : ∀ x b, 0 ≤ w x b) (hw1 : ∀ x, w x false + w x true = 1)
    (𝒜 ℬ : Finset (Finset β)) :
    wdpairs w 𝒜 ℬ ≤ fmarg w 𝒜 * fmarg w ℬ :=
  wdpairs_le_mul_of_doubled_independence hw0 hw1 𝒜 ℬ















































end StatMech

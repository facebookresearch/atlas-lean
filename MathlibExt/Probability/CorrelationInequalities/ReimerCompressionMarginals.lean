/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.CorrelationInequalities.ReimerDoubledEvents
public import MathlibExt.Probability.CorrelationInequalities.ReimerSymmetricWeights

/-!
# Weighted marginals under up-, down- and double compression

For a product weight `w` on `α → Bool`, `fmarg w 𝒜` is the weight of the family `𝒜` of supports.
Down-compression at `a` does not decrease `fmarg w 𝒜` when `w a true ≤ w a false`
(`fmarg_le_downComp`, in `ReimerIteratedCompression`); this file proves the dual statement for
up-compression (`fmarg_le_upCompression`, when `w a false ≤ w a true`) and combines the two into
the double compression `doubleCompress i` on the doubled ground set `β ⊕ β` (down at `inl i`, up
at `inr i`) and its iterates `iterDoubleCompress`. For symmetric weights double compression
preserves `fmarg`, and the doubled marginal of `boxDoubled 𝒜 ℬ` (which is `wdpairs w 𝒜 ℬ`) only
grows along iterated double compression.

## Main definitions

* `iterDoubleCompress is 𝒰`: apply `doubleCompress i` for `i` in the list `is`.

## Main results

* `fmarg_le_upCompression`, `fmarg_le_doubleCompress`, `fmarg_le_iterDoubleCompress`.
* `fmarg_doubleCompress_symm_eq`: double compression preserves `fmarg` for symmetric weights.
* `wdpairs_le_iterDoubleCompress_of_symm`: for symmetric weights,
  `wdpairs w 𝒜 ℬ ≤ fmarg (doubleWeight w) (iterDoubleCompress is (boxDoubled 𝒜 ℬ))`.
-/

@[expose] public section

open Finset
open scoped FinsetFamily

namespace StatMech

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Exchange identity for `fwt` when adding a coordinate `a ∉ t` to the support. -/
lemma fwt_insert_mul (w : α → Bool → ℝ) {t : Finset α} {a : α} (ha : a ∉ t) :
    fwt w (insert a t) * w a false = fwt w t * w a true := by
  have h1 : fwt w (insert a t) = w a true * fwt' w a t := by
    rw [fwt_of_mem w (Finset.mem_insert_self a t), Finset.erase_insert ha]
  have h2 : fwt w t = w a false * fwt' w a t := fwt_of_notMem w ha
  rw [h1, h2]; ring

/-- Removing `a` from a support does not decrease its weight when `w a true ≤ w a false`. -/
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

/-- Adding `a` to a support does not decrease its weight when `w a false ≤ w a true`. -/
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
/-- If `s ∈ 𝒜` but `s.erase a ∉ 𝒜`, then `a ∈ s`. -/
lemma mem_of_erase_notMem {a : α} {𝒜 : Finset (Finset α)} {s : Finset α}
    (hs : s ∈ 𝒜) (h : s.erase a ∉ 𝒜) : a ∈ s := by
  by_contra ha
  rw [Finset.erase_eq_of_notMem ha] at h
  exact h hs

omit [Fintype α] in
/-- If `s ∈ 𝒜` but its up-compression at `a` is not, then `a ∉ s`. -/
lemma notMem_of_compress_notMem {a : α} {𝒜 : Finset (Finset α)} {s : Finset α}
    (hs : s ∈ 𝒜) (h : UV.compress ({a} : Finset α) ∅ s ∉ 𝒜) : a ∉ s := by
  intro ha
  rw [uvCompress_singleton_empty, Finset.insert_eq_of_mem ha] at h
  exact h hs

/-- Up-compression at `a` does not decrease `fmarg w` when `w a false ≤ w a true`. Dual of
`fmarg_le_downComp`. -/
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
      rw [uvCompress_singleton_empty]
    · intro s hs t ht heq
      simp only [hR, Finset.mem_coe, Finset.mem_filter] at hs ht
      have has := notMem_of_compress_notMem hs.1 hs.2
      have hat := notMem_of_compress_notMem ht.1 ht.2
      simp only [hc, uvCompress_singleton_empty] at heq
      have hh : (insert a s).erase a = (insert a t).erase a := by rw [heq]
      rwa [Finset.erase_insert has, Finset.erase_insert hat] at hh
  rw [hsplit, hcomp, hQR]
  refine add_le_add (le_refl _) (Finset.sum_le_sum (fun s hs => ?_))
  rw [hR, Finset.mem_filter] at hs
  exact fwt_le_insert hw0 hdom (notMem_of_compress_notMem hs.1 hs.2)

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- Double compression at `i` does not decrease `fmarg w` when `inl i` favors `false` and `inr i`
favors `true`. -/
theorem fmarg_le_doubleCompress {w : (β ⊕ β) → Bool → ℝ} (hw0 : ∀ x b, 0 ≤ w x b) (i : β)
    (hL : w (Sum.inl i) true ≤ w (Sum.inl i) false)
    (hR : w (Sum.inr i) false ≤ w (Sum.inr i) true)
    (𝒰 : Finset (Finset (β ⊕ β))) :
    fmarg w 𝒰 ≤ fmarg w (doubleCompress i 𝒰) := by
  unfold doubleCompress upRight upComp downLeft
  calc fmarg w 𝒰
      ≤ fmarg w (Down.compression (Sum.inl i) 𝒰) := fmarg_le_downComp hw0 _ hL 𝒰
    _ ≤ fmarg w (UV.compression ({Sum.inr i} : Finset (β ⊕ β)) ∅
                  (Down.compression (Sum.inl i) 𝒰)) :=
        fmarg_le_upCompression hw0 _ hR _

/-- Iterated double compression along the list `is` (rightmost coordinate first). -/
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
/-- Iterated double compression preserves cardinality. -/
theorem iterDoubleCompress_card (is : List β) (𝒰 : Finset (Finset (β ⊕ β))) :
    (iterDoubleCompress is 𝒰).card = 𝒰.card := by
  induction is with
  | nil => rfl
  | cons i is ih => rw [iterDoubleCompress_cons, doubleCompress_card, ih]

/-- Iterated double compression does not decrease `fmarg w` under the coordinatewise dominance
hypotheses of `fmarg_le_doubleCompress`. -/
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

/-- `fmarg_le_downComp` for the constant weight `1` (counting measure). -/
theorem fmarg_le_downCompression_satisfiable (a : α) (𝒜 : Finset (Finset α)) :
    fmarg (fun _ _ => (1 : ℝ)) 𝒜 ≤ fmarg (fun _ _ => (1 : ℝ)) (Down.compression a 𝒜) :=
  fmarg_le_downComp (fun _ _ => zero_le_one) a (le_refl _) 𝒜

/-- `fmarg_le_doubleCompress` for symmetric weights. -/
theorem fmarg_le_doubleCompress_symm {w : (β ⊕ β) → Bool → ℝ} (hw0 : ∀ x b, 0 ≤ w x b)
    (hsym : ∀ x, w x false = w x true) (i : β) (𝒰 : Finset (Finset (β ⊕ β))) :
    fmarg w 𝒰 ≤ fmarg w (doubleCompress i 𝒰) :=
  fmarg_le_doubleCompress hw0 i (le_of_eq (hsym _).symm) (le_of_eq (hsym _)) 𝒰

/-- For symmetric weights double compression preserves `fmarg`. See also
`fmarg_symm_eq_const_mul_card`. -/
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

/-- For symmetric weights, the weighted disjoint-pair count is at most the doubled marginal of any
iterated double compression of `boxDoubled 𝒜 ℬ`. -/
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
  rwa [fmarg_boxDoubled] at hkey

end StatMech

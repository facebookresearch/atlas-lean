/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































import Code.Universality.HexLattice
import Code.Universality.HexVertex
import Code.Universality.HexVertexEnum

namespace StatMech.Universality

open Complex
open Function
open HexWalk










variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


abbrev SlotType (E : HexVertexEnumeration region a h0 v du) : Type :=
  (E.pairs × Bool) ⊕ (E.triplets × Fin 3)
















theorem hinj_of_leftInverse (E : HexVertexEnumeration region a h0 v du)
    (cls : List ℤ → SlotType E)
    (hleft : ∀ slot ∈ Function.support (combinedSummand region a h0 v du ∘ E.slotTurns),
        cls (E.slotTurns slot) = slot) :
    Function.Injective
      fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) =>
        E.slotTurns x.1 := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  simp only at h
  apply Subtype.ext
  have hc : cls (E.slotTurns x) = cls (E.slotTurns y) := by rw [h]
  rw [hleft x hx, hleft y hy] at hc
  exact hc





theorem hsub_of_rightInverse (E : HexVertexEnumeration region a h0 v du)
    (cls : List ℤ → SlotType E)
    (hright : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        E.slotTurns (cls ts) = ts) :
    Function.support (combinedSummand region a h0 v du) ⊆
      Set.range fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) =>
        E.slotTurns x.1 := by
  intro ts hts
  have hst : E.slotTurns (cls ts) = ts := hright ts hts
  have hmem : cls ts ∈ Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) := by
    simp only [Function.mem_support, Function.comp_apply, hst]
    exact hts
  exact ⟨⟨cls ts, hmem⟩, hst⟩

























structure HexVertexBijection (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (v du : ℂ) where
  

  enum : HexVertexEnumeration region a h0 v du
  
  classify : List ℤ → SlotType enum
  


  classify_slotTurns : ∀ slot ∈ Function.support
      (combinedSummand region a h0 v du ∘ enum.slotTurns),
    classify (enum.slotTurns slot) = slot
  

  slotTurns_classify : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
    enum.slotTurns (classify ts) = ts

namespace HexVertexBijection

variable (B : HexVertexBijection region a h0 v du)



theorem hinj :
    Function.Injective
      fun x : Function.support (combinedSummand region a h0 v du ∘ B.enum.slotTurns) =>
        B.enum.slotTurns x.1 :=
  hinj_of_leftInverse B.enum B.classify B.classify_slotTurns



theorem hsub :
    Function.support (combinedSummand region a h0 v du) ⊆
      Set.range fun x : Function.support (combinedSummand region a h0 v du ∘ B.enum.slotTurns) =>
        B.enum.slotTurns x.1 :=
  hsub_of_rightInverse B.enum B.classify B.slotTurns_classify
















theorem relation (B : HexVertexBijection region a h0 v du) (hdu : du ≠ 0)
    (hp : Summable fun ts => parafSummand region a h0 (v + du) (5/8) hexChi ts)
    (hq : Summable fun ts => parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi ts)
    (hr : Summable fun ts => parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts) :
    ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 :=
  HexVertexEnumeration.relation_of_bijection B.enum hdu hp hq hr B.hinj B.hsub

end HexVertexBijection















def slotLabel {E : HexVertexEnumeration region a h0 v du} :
    ((E.pairs × Bool) ⊕ (E.triplets × Fin 3)) → Fin 3
  | Sum.inl (_, false) => 1
  | Sum.inl (_, true)  => 2
  | Sum.inr (_, ⟨0, _⟩) => 0
  | Sum.inr (_, ⟨1, _⟩) => 1
  | Sum.inr (_, _)      => 2



noncomputable def labelMid (v du : ℂ) : Fin 3 → ℂ
  | ⟨0, _⟩ => v + du
  | ⟨1, _⟩ => v + hexOmega * du
  | _      => v + hexOmega ^ 2 * du




theorem slot_endsAt_label (E : HexVertexEnumeration region a h0 v du)
    (slot : (E.pairs × Bool) ⊕ (E.triplets × Fin 3)) :
    (ofTurns a h0 (E.slotTurns slot)).EndsAt (labelMid v du (slotLabel slot)) := by
  rcases slot with (⟨P, b⟩ | ⟨T, i⟩)
  · cases b with
    | false => exact (E.pairQ_valid P P.2).2.2
    | true  => exact (E.pairR_valid P P.2).2.2
  · match i with
    | ⟨0, _⟩ => exact (E.tripP_valid T T.2).2.2
    | ⟨1, _⟩ => exact (E.tripQ_valid T T.2).2.2
    | ⟨2, _⟩ => exact (E.tripR_valid T T.2).2.2



theorem labelMid_injective (hdu : du ≠ 0) : Function.Injective (labelMid v du) := by
  intro i j h
  match i, j with
  | ⟨0, _⟩, ⟨0, _⟩ => rfl
  | ⟨1, _⟩, ⟨1, _⟩ => rfl
  | ⟨2, _⟩, ⟨2, _⟩ => rfl
  | ⟨0, _⟩, ⟨1, _⟩ => exact absurd h (hexMid_p_ne_q hdu)
  | ⟨0, _⟩, ⟨2, _⟩ => exact absurd h (hexMid_p_ne_r hdu)
  | ⟨1, _⟩, ⟨0, _⟩ => exact absurd h (fun hh => hexMid_p_ne_q hdu hh.symm)
  | ⟨1, _⟩, ⟨2, _⟩ => exact absurd h (hexMid_q_ne_r hdu)
  | ⟨2, _⟩, ⟨0, _⟩ => exact absurd h (fun hh => hexMid_p_ne_r hdu hh.symm)
  | ⟨2, _⟩, ⟨1, _⟩ => exact absurd h (fun hh => hexMid_q_ne_r hdu hh.symm)




theorem slotLabel_eq_of_slotTurns_eq (E : HexVertexEnumeration region a h0 v du)
    (hdu : du ≠ 0) (s1 s2 : (E.pairs × Bool) ⊕ (E.triplets × Fin 3))
    (h : E.slotTurns s1 = E.slotTurns s2) : slotLabel s1 = slotLabel s2 := by
  apply labelMid_injective hdu
  have h1 := slot_endsAt_label E s1
  have h2 := slot_endsAt_label E s2
  unfold HexWalk.EndsAt at h1 h2
  rw [← h1, ← h2, h]











theorem support_endsAt_threeMid (ts : List ℤ)
    (h : ts ∈ Function.support (combinedSummand region a h0 v du)) :
    (ofTurns a h0 ts).EndsAt (v + du) ∨ (ofTurns a h0 ts).EndsAt (v + hexOmega * du)
      ∨ (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) := by
  by_contra hcon
  rw [not_or, not_or] at hcon
  obtain ⟨hnp, hnq, hnr⟩ := hcon
  apply h
  show combinedSummand region a h0 v du ts = 0
  unfold combinedSummand
  rw [parafSummand_eq_zero_of_not_endsAt region a h0 (v + du) _ _ ts hnp,
      parafSummand_eq_zero_of_not_endsAt region a h0 (v + hexOmega * du) _ _ ts hnq,
      parafSummand_eq_zero_of_not_endsAt region a h0 (v + hexOmega ^ 2 * du) _ _ ts hnr]
  ring




theorem support_isLegalSAW (ts : List ℤ)
    (h : ts ∈ Function.support (combinedSummand region a h0 v du))
    (hp : (ofTurns a h0 ts).EndsAt (v + du)) (hdu : du ≠ 0) :
    (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn region := by
  have hcs : combinedSummand region a h0 v du ts
      = ((v + du) - v) * parafSummand region a h0 (v + du) (5/8) hexChi ts :=
    combinedSummand_at_p hdu hp
  have hne : parafSummand region a h0 (v + du) (5/8) hexChi ts ≠ 0 := by
    intro hz
    apply h
    show combinedSummand region a h0 v du ts = 0
    rw [hcs, hz, mul_zero]
  unfold parafSummand at hne
  by_contra hcon
  rw [not_and_or] at hcon
  apply hne
  rw [if_neg]
  rintro ⟨h1, h2, _⟩
  rcases hcon with h1' | h2'
  · exact h1' h1
  · exact h2' h2















theorem hinj_of_perLabel (E : HexVertexEnumeration region a h0 v du) (hdu : du ≠ 0)
    (hlabel : ∀ s1 s2 : (E.pairs × Bool) ⊕ (E.triplets × Fin 3),
        slotLabel s1 = slotLabel s2 → E.slotTurns s1 = E.slotTurns s2 → s1 = s2) :
    Function.Injective
      fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) =>
        E.slotTurns x.1 := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  simp only at h
  apply Subtype.ext
  exact hlabel x y (slotLabel_eq_of_slotTurns_eq E hdu x y h) h




theorem hinj_of_injective (E : HexVertexEnumeration region a h0 v du)
    (hsti : Function.Injective E.slotTurns) :
    Function.Injective
      fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) =>
        E.slotTurns x.1 := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  simp only at h
  exact Subtype.ext (hsti h)

















noncomputable def HexVertexBijection.ofInjectiveRightInverse
    (E : HexVertexEnumeration region a h0 v du)
    (classify : List ℤ → SlotType E)
    (hsti : Function.Injective E.slotTurns)
    (hright : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        E.slotTurns (classify ts) = ts) :
    HexVertexBijection region a h0 v du where
  enum := E
  classify := classify
  classify_slotTurns := by
    intro slot hslot
    have hf : E.slotTurns slot ∈ Function.support (combinedSummand region a h0 v du) := by
      rw [Function.mem_support] at hslot ⊢
      exact hslot
    exact hsti (hright (E.slotTurns slot) hf)
  slotTurns_classify := hright






















theorem hlabel_tripletOnly (E : HexVertexEnumeration region a h0 v du)
    (hnopairs : E.pairs = ∅)
    (htinj : ∀ T1 T2 : E.triplets, E.tripBase T1 = E.tripBase T2 → T1 = T2) :
    ∀ s1 s2 : (E.pairs × Bool) ⊕ (E.triplets × Fin 3),
        slotLabel s1 = slotLabel s2 → E.slotTurns s1 = E.slotTurns s2 → s1 = s2 := by
  rintro (⟨P, _⟩ | ⟨T1, i1⟩) s2 hlab hst
  · exact absurd (hnopairs ▸ P.2 : (P : ℕ) ∈ (∅ : Finset ℕ)) (by simp)
  · rcases s2 with (⟨P, _⟩ | ⟨T2, i2⟩)
    · exact absurd (hnopairs ▸ P.2 : (P : ℕ) ∈ (∅ : Finset ℕ)) (by simp)
    · match i1, i2 with
      | ⟨0, _⟩, ⟨0, _⟩ =>
        have hb : E.tripBase T1 = E.tripBase T2 := hst
        have := htinj T1 T2 hb; subst this; rfl
      | ⟨1, _⟩, ⟨1, _⟩ =>
        have hb : E.tripBase T1 = E.tripBase T2 := (List.append_left_inj _).mp hst
        have := htinj T1 T2 hb; subst this; rfl
      | ⟨2, _⟩, ⟨2, _⟩ =>
        have hb : E.tripBase T1 = E.tripBase T2 := (List.append_left_inj _).mp hst
        have := htinj T1 T2 hb; subst this; rfl
      | ⟨0, _⟩, ⟨1, _⟩ => simp [slotLabel] at hlab
      | ⟨0, _⟩, ⟨2, _⟩ => simp [slotLabel] at hlab
      | ⟨1, _⟩, ⟨0, _⟩ => simp [slotLabel] at hlab
      | ⟨1, _⟩, ⟨2, _⟩ => simp [slotLabel] at hlab
      | ⟨2, _⟩, ⟨0, _⟩ => simp [slotLabel] at hlab
      | ⟨2, _⟩, ⟨1, _⟩ => simp [slotLabel] at hlab






theorem hinj_tripletOnly (E : HexVertexEnumeration region a h0 v du) (hdu : du ≠ 0)
    (hnopairs : E.pairs = ∅)
    (htinj : ∀ T1 T2 : E.triplets, E.tripBase T1 = E.tripBase T2 → T1 = T2) :
    Function.Injective
      fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) =>
        E.slotTurns x.1 :=
  hinj_of_perLabel E hdu (hlabel_tripletOnly E hnopairs htinj)















theorem hlabel_pairOnly (E : HexVertexEnumeration region a h0 v du)
    (hnotrip : E.triplets = ∅)
    (hqinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLq P1 = E.pairBase P2 ++ E.pairLq P2 → P1 = P2)
    (hrinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLr P1 = E.pairBase P2 ++ E.pairLr P2 → P1 = P2) :
    ∀ s1 s2 : (E.pairs × Bool) ⊕ (E.triplets × Fin 3),
        slotLabel s1 = slotLabel s2 → E.slotTurns s1 = E.slotTurns s2 → s1 = s2 := by
  rintro (⟨P1, b1⟩ | ⟨T, _⟩) s2 hlab hst
  · rcases s2 with (⟨P2, b2⟩ | ⟨T, _⟩)
    · cases b1 <;> cases b2
      · have := hqinj P1 P2 hst; subst this; rfl
      · simp [slotLabel] at hlab
      · simp [slotLabel] at hlab
      · have := hrinj P1 P2 hst; subst this; rfl
    · exact absurd (hnotrip ▸ T.2 : (T : ℕ) ∈ (∅ : Finset ℕ)) (by simp)
  · exact absurd (hnotrip ▸ T.2 : (T : ℕ) ∈ (∅ : Finset ℕ)) (by simp)





theorem hinj_pairOnly (E : HexVertexEnumeration region a h0 v du) (hdu : du ≠ 0)
    (hnotrip : E.triplets = ∅)
    (hqinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLq P1 = E.pairBase P2 ++ E.pairLq P2 → P1 = P2)
    (hrinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLr P1 = E.pairBase P2 ++ E.pairLr P2 → P1 = P2) :
    Function.Injective
      fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) =>
        E.slotTurns x.1 :=
  hinj_of_perLabel E hdu (hlabel_pairOnly E hnotrip hqinj hrinj)























theorem hlabel_general (E : HexVertexEnumeration region a h0 v du)
    (htinj : ∀ T1 T2 : E.triplets, E.tripBase T1 = E.tripBase T2 → T1 = T2)
    (hqinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLq P1 = E.pairBase P2 ++ E.pairLq P2 → P1 = P2)
    (hrinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLr P1 = E.pairBase P2 ++ E.pairLr P2 → P1 = P2)
    (hqcross : ∀ (P : E.pairs) (T : E.triplets),
        E.pairBase P ++ E.pairLq P ≠ E.tripBase T ++ [-1])
    (hrcross : ∀ (P : E.pairs) (T : E.triplets),
        E.pairBase P ++ E.pairLr P ≠ E.tripBase T ++ [1]) :
    ∀ s1 s2 : (E.pairs × Bool) ⊕ (E.triplets × Fin 3),
        slotLabel s1 = slotLabel s2 → E.slotTurns s1 = E.slotTurns s2 → s1 = s2 := by
  rintro (⟨P1, b1⟩ | ⟨T1, i1⟩) (⟨P2, b2⟩ | ⟨T2, i2⟩) hlab hst
  · cases b1 <;> cases b2
    · have := hqinj P1 P2 hst; subst this; rfl
    · simp [slotLabel] at hlab
    · simp [slotLabel] at hlab
    · have := hrinj P1 P2 hst; subst this; rfl
  · cases b1
    · match i2 with
      | ⟨1, _⟩ => exact absurd hst (hqcross P1 T2)
      | ⟨0, _⟩ => simp [slotLabel] at hlab
      | ⟨2, _⟩ => simp [slotLabel] at hlab
    · match i2 with
      | ⟨2, _⟩ => exact absurd hst (hrcross P1 T2)
      | ⟨0, _⟩ => simp [slotLabel] at hlab
      | ⟨1, _⟩ => simp [slotLabel] at hlab
  · cases b2
    · match i1 with
      | ⟨1, _⟩ => exact absurd hst.symm (hqcross P2 T1)
      | ⟨0, _⟩ => simp [slotLabel] at hlab
      | ⟨2, _⟩ => simp [slotLabel] at hlab
    · match i1 with
      | ⟨2, _⟩ => exact absurd hst.symm (hrcross P2 T1)
      | ⟨0, _⟩ => simp [slotLabel] at hlab
      | ⟨1, _⟩ => simp [slotLabel] at hlab
  · match i1, i2 with
    | ⟨0, _⟩, ⟨0, _⟩ => have := htinj T1 T2 hst; subst this; rfl
    | ⟨1, _⟩, ⟨1, _⟩ => have := htinj T1 T2 ((List.append_left_inj _).mp hst); subst this; rfl
    | ⟨2, _⟩, ⟨2, _⟩ => have := htinj T1 T2 ((List.append_left_inj _).mp hst); subst this; rfl
    | ⟨0, _⟩, ⟨1, _⟩ => simp [slotLabel] at hlab
    | ⟨0, _⟩, ⟨2, _⟩ => simp [slotLabel] at hlab
    | ⟨1, _⟩, ⟨0, _⟩ => simp [slotLabel] at hlab
    | ⟨1, _⟩, ⟨2, _⟩ => simp [slotLabel] at hlab
    | ⟨2, _⟩, ⟨0, _⟩ => simp [slotLabel] at hlab
    | ⟨2, _⟩, ⟨1, _⟩ => simp [slotLabel] at hlab







theorem hinj_general (E : HexVertexEnumeration region a h0 v du) (hdu : du ≠ 0)
    (htinj : ∀ T1 T2 : E.triplets, E.tripBase T1 = E.tripBase T2 → T1 = T2)
    (hqinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLq P1 = E.pairBase P2 ++ E.pairLq P2 → P1 = P2)
    (hrinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLr P1 = E.pairBase P2 ++ E.pairLr P2 → P1 = P2)
    (hqcross : ∀ (P : E.pairs) (T : E.triplets),
        E.pairBase P ++ E.pairLq P ≠ E.tripBase T ++ [-1])
    (hrcross : ∀ (P : E.pairs) (T : E.triplets),
        E.pairBase P ++ E.pairLr P ≠ E.tripBase T ++ [1]) :
    Function.Injective
      fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) =>
        E.slotTurns x.1 :=
  hinj_of_perLabel E hdu (hlabel_general E htinj hqinj hrinj hqcross hrcross)

















theorem hsub_of_coverage (E : HexVertexEnumeration region a h0 v du)
    (covp : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + du) →
        ∃ slot : SlotType E, E.slotTurns slot = ts)
    (covq : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + hexOmega * du) →
        ∃ slot : SlotType E, E.slotTurns slot = ts)
    (covr : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) →
        ∃ slot : SlotType E, E.slotTurns slot = ts) :
    Function.support (combinedSummand region a h0 v du) ⊆
      Set.range fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) =>
        E.slotTurns x.1 := by
  intro ts hts
  have hslot : ∃ slot : SlotType E, E.slotTurns slot = ts := by
    rcases support_endsAt_threeMid ts hts with hp | hq | hr
    · exact covp ts hts hp
    · exact covq ts hts hq
    · exact covr ts hts hr
  obtain ⟨slot, hsl⟩ := hslot
  have hmem : slot ∈ Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) := by
    simp only [Function.mem_support, Function.comp_apply, hsl]
    exact hts
  exact ⟨⟨slot, hmem⟩, hsl⟩


















theorem relation_of_partitionFacts (E : HexVertexEnumeration region a h0 v du)
    (hdu : du ≠ 0)
    (hp : Summable fun ts => parafSummand region a h0 (v + du) (5/8) hexChi ts)
    (hq : Summable fun ts => parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi ts)
    (hr : Summable fun ts => parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts)
    (htinj : ∀ T1 T2 : E.triplets, E.tripBase T1 = E.tripBase T2 → T1 = T2)
    (hqinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLq P1 = E.pairBase P2 ++ E.pairLq P2 → P1 = P2)
    (hrinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLr P1 = E.pairBase P2 ++ E.pairLr P2 → P1 = P2)
    (hqcross : ∀ (P : E.pairs) (T : E.triplets),
        E.pairBase P ++ E.pairLq P ≠ E.tripBase T ++ [-1])
    (hrcross : ∀ (P : E.pairs) (T : E.triplets),
        E.pairBase P ++ E.pairLr P ≠ E.tripBase T ++ [1])
    (covp : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + du) → ∃ slot : SlotType E, E.slotTurns slot = ts)
    (covq : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + hexOmega * du) →
        ∃ slot : SlotType E, E.slotTurns slot = ts)
    (covr : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) →
        ∃ slot : SlotType E, E.slotTurns slot = ts) :
    ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 :=
  HexVertexEnumeration.relation_of_bijection E hdu hp hq hr
    (hinj_general E hdu htinj hqinj hrinj hqcross hrcross)
    (hsub_of_coverage E covp covq covr)














theorem parafSummand_emptyRegion (a : ℂ) (h0 : ℤ) (z : ℂ) (σ x : ℝ) (ts : List ℤ) :
    parafSummand (fun _ => False) a h0 z σ x ts = 0 := by
  unfold parafSummand
  rw [if_neg]
  rintro ⟨_, hstay, _⟩
  have hne : (ofTurns a h0 ts).mids ≠ [] := by
    intro h
    have := HexWalk.length_mids (ofTurns a h0 ts)
    rw [h] at this; simp at this
  obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil _ hne
  exact hstay m hm


theorem parafObservable_emptyRegion (a : ℂ) (h0 : ℤ) (z : ℂ) (σ x : ℝ) :
    parafObservable (fun _ => False) a h0 z σ x = 0 := by
  unfold parafObservable
  rw [show (fun ts => parafSummand (fun _ => False) a h0 z σ x ts) = (fun _ => (0 : ℂ)) from
    funext fun ts => parafSummand_emptyRegion a h0 z σ x ts]
  exact tsum_zero



theorem combinedSummand_emptyRegion (a : ℂ) (h0 : ℤ) (v du : ℂ) (ts : List ℤ) :
    combinedSummand (fun _ => False) a h0 v du ts = 0 := by
  unfold combinedSummand
  rw [parafSummand_emptyRegion, parafSummand_emptyRegion, parafSummand_emptyRegion]
  ring



theorem summable_emptyRegion (a : ℂ) (h0 : ℤ) (z : ℂ) (σ x : ℝ) :
    Summable fun ts => parafSummand (fun _ => False) a h0 z σ x ts := by
  rw [show (fun ts => parafSummand (fun _ => False) a h0 z σ x ts) = (fun _ => (0 : ℂ)) from
    funext fun ts => parafSummand_emptyRegion a h0 z σ x ts]
  exact summable_zero


noncomputable def emptyEnumeration (a : ℂ) (h0 : ℤ) (v du : ℂ) :
    HexVertexEnumeration (fun _ => False) a h0 v du :=
  HexVertexEnumeration.empty (fun _ => False) a h0 v du
    (fun z => parafObservable_emptyRegion a h0 z _ _)







theorem relation_emptyRegion (a : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0) :
    ((v + du) - v) * parafObservable (fun _ => False) a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v)
          * parafObservable (fun _ => False) a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable (fun _ => False) a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 :=
  relation_of_partitionFacts (emptyEnumeration a h0 v du) hdu
    (summable_emptyRegion a h0 _ _ _) (summable_emptyRegion a h0 _ _ _)
    (summable_emptyRegion a h0 _ _ _)
    (fun T1 _ _ => absurd T1.2 (Finset.notMem_empty _))
    (fun P1 _ _ => absurd P1.2 (Finset.notMem_empty _))
    (fun P1 _ _ => absurd P1.2 (Finset.notMem_empty _))
    (fun P _ => absurd P.2 (Finset.notMem_empty _))
    (fun P _ => absurd P.2 (Finset.notMem_empty _))
    (fun ts hts _ => absurd (combinedSummand_emptyRegion a h0 v du ts) hts)
    (fun ts hts _ => absurd (combinedSummand_emptyRegion a h0 v du ts) hts)
    (fun ts hts _ => absurd (combinedSummand_emptyRegion a h0 v du ts) hts)

end StatMech.Universality

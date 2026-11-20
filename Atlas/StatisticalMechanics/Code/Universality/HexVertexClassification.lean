/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































































import Code.Universality.HexLattice
import Code.Universality.HexVertex
import Code.Universality.HexVertexEnum
import Code.Universality.HexVertexBijection
import Code.Universality.HexVertexSeparation
import Code.Universality.HexVertexCoverage

namespace StatMech.Universality

open Complex
open Function
open HexWalk

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}














theorem hexClass_endsAt_passesThrough (ts : List ℤ) (z : ℂ)
    (h : (ofTurns a h0 ts).EndsAt z) : PassesThrough a h0 ts z := by
  unfold PassesThrough
  unfold HexWalk.EndsAt at h
  have hne : (ofTurns a h0 ts).mids ≠ [] := by
    intro hnil
    have := HexWalk.length_mids (ofTurns a h0 ts)
    rw [hnil] at this
    simp at this
  rw [← h]
  exact List.getLast_mem hne





theorem hexClass_specialMidCount_three_of_passes (ts : List ℤ)
    (hp : PassesThrough a h0 ts (v + du))
    (hq : PassesThrough a h0 ts (v + hexOmega * du))
    (hr : PassesThrough a h0 ts (v + hexOmega ^ 2 * du)) :
    specialMidCount a h0 v du ts = 3 := by
  classical
  unfold specialMidCount
  rw [if_pos hp, if_pos hq, if_pos hr]

























structure HexSawClassification (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (v du : ℂ) where
  
  pairs : Finset ℕ
  
  pairBase : ℕ → List ℤ
  
  pairLq : ℕ → List ℤ
  
  pairLr : ℕ → List ℤ
  
  pairLq_sum : ∀ P ∈ pairs, (pairLq P).sum = -4
  
  pairLr_sum : ∀ P ∈ pairs, (pairLr P).sum = 4
  
  pairLen : ∀ P ∈ pairs, (pairLq P).length = (pairLr P).length
  
  pairQ_valid : ∀ P ∈ pairs,
    (ofTurns a h0 (pairBase P ++ pairLq P)).IsLegalSAW
      ∧ (ofTurns a h0 (pairBase P ++ pairLq P)).StaysIn region
      ∧ (ofTurns a h0 (pairBase P ++ pairLq P)).EndsAt (v + hexOmega * du)
  
  pairR_valid : ∀ P ∈ pairs,
    (ofTurns a h0 (pairBase P ++ pairLr P)).IsLegalSAW
      ∧ (ofTurns a h0 (pairBase P ++ pairLr P)).StaysIn region
      ∧ (ofTurns a h0 (pairBase P ++ pairLr P)).EndsAt (v + hexOmega ^ 2 * du)
  


  pairQ_passes_p : ∀ P ∈ pairs, PassesThrough a h0 (pairBase P ++ pairLq P) (v + du)
  

  pairQ_passes_r : ∀ P ∈ pairs,
    PassesThrough a h0 (pairBase P ++ pairLq P) (v + hexOmega ^ 2 * du)
  

  pairR_passes_p : ∀ P ∈ pairs, PassesThrough a h0 (pairBase P ++ pairLr P) (v + du)
  

  pairR_passes_q : ∀ P ∈ pairs,
    PassesThrough a h0 (pairBase P ++ pairLr P) (v + hexOmega * du)
  
  triplets : Finset ℕ
  
  tripBase : ℕ → List ℤ
  
  tripP_valid : ∀ T ∈ triplets,
    (ofTurns a h0 (tripBase T)).IsLegalSAW
      ∧ (ofTurns a h0 (tripBase T)).StaysIn region
      ∧ (ofTurns a h0 (tripBase T)).EndsAt (v + du)
  
  tripQ_valid : ∀ T ∈ triplets,
    (ofTurns a h0 (tripBase T ++ [-1])).IsLegalSAW
      ∧ (ofTurns a h0 (tripBase T ++ [-1])).StaysIn region
      ∧ (ofTurns a h0 (tripBase T ++ [-1])).EndsAt (v + hexOmega * du)
  
  tripR_valid : ∀ T ∈ triplets,
    (ofTurns a h0 (tripBase T ++ [1])).IsLegalSAW
      ∧ (ofTurns a h0 (tripBase T ++ [1])).StaysIn region
      ∧ (ofTurns a h0 (tripBase T ++ [1])).EndsAt (v + hexOmega ^ 2 * du)
  


  tripQ_not_passes_r : ∀ T ∈ triplets,
    ¬ PassesThrough a h0 (tripBase T ++ [-1]) (v + hexOmega ^ 2 * du)
  

  tripR_not_passes_q : ∀ T ∈ triplets,
    ¬ PassesThrough a h0 (tripBase T ++ [1]) (v + hexOmega * du)
  
  tripBase_inj : ∀ T1 T2 : triplets, tripBase T1 = tripBase T2 → T1 = T2
  
  pairQ_inj : ∀ P1 P2 : pairs,
    pairBase P1 ++ pairLq P1 = pairBase P2 ++ pairLq P2 → P1 = P2
  
  pairR_inj : ∀ P1 P2 : pairs,
    pairBase P1 ++ pairLr P1 = pairBase P2 ++ pairLr P2 → P1 = P2
  


  classify_p : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
    (ofTurns a h0 ts).EndsAt (v + du) →
    ∃ T : ℕ, T ∈ triplets ∧ tripBase T = ts
  


  classify_q : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
    (ofTurns a h0 ts).EndsAt (v + hexOmega * du) →
    (∃ T : ℕ, T ∈ triplets ∧ tripBase T ++ [-1] = ts)
      ∨ (∃ P : ℕ, P ∈ pairs ∧ pairBase P ++ pairLq P = ts)
  


  classify_r : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
    (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) →
    (∃ T : ℕ, T ∈ triplets ∧ tripBase T ++ [1] = ts)
      ∨ (∃ P : ℕ, P ∈ pairs ∧ pairBase P ++ pairLr P = ts)
  



  reindex :
    (((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v) * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi)
    = (∑ P ∈ pairs,
        (((v + hexOmega * du) - v)
            * parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi (pairBase P ++ pairLq P)
          + ((v + hexOmega ^ 2 * du) - v)
              * parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi (pairBase P ++ pairLr P)))
      + (∑ T ∈ triplets,
          (((v + du) - v) * parafSummand region a h0 (v + du) (5/8) hexChi (tripBase T)
            + ((v + hexOmega * du) - v)
                * parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi (tripBase T ++ [-1])
            + ((v + hexOmega ^ 2 * du) - v)
                * parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi (tripBase T ++ [1])))

namespace HexSawClassification

variable (C : HexSawClassification region a h0 v du)





def toEnum : HexVertexEnumeration region a h0 v du where
  pairs := C.pairs
  pairBase := C.pairBase
  pairLq := C.pairLq
  pairLr := C.pairLr
  pairLq_sum := C.pairLq_sum
  pairLr_sum := C.pairLr_sum
  pairLen := C.pairLen
  pairQ_valid := C.pairQ_valid
  pairR_valid := C.pairR_valid
  triplets := C.triplets
  tripBase := C.tripBase
  tripP_valid := C.tripP_valid
  tripQ_valid := C.tripQ_valid
  tripR_valid := C.tripR_valid
  reindex := C.reindex

@[simp] theorem toEnum_pairs : C.toEnum.pairs = C.pairs := rfl
@[simp] theorem toEnum_triplets : C.toEnum.triplets = C.triplets := rfl
@[simp] theorem toEnum_pairBase : C.toEnum.pairBase = C.pairBase := rfl
@[simp] theorem toEnum_pairLq : C.toEnum.pairLq = C.pairLq := rfl
@[simp] theorem toEnum_pairLr : C.toEnum.pairLr = C.pairLr := rfl
@[simp] theorem toEnum_tripBase : C.toEnum.tripBase = C.tripBase := rfl

end HexSawClassification















theorem hexClass_separated (C : HexSawClassification region a h0 v du) :
    HexVertexSeparated C.toEnum where
  pairQ_count_three := by
    intro P hP
    simp only [HexSawClassification.toEnum_pairBase, HexSawClassification.toEnum_pairLq]
    have hPmem : P ∈ C.pairs := by simpa using hP
    refine hexClass_specialMidCount_three_of_passes _ ?_ ?_ ?_
    · exact C.pairQ_passes_p P hPmem
    · exact hexClass_endsAt_passesThrough _ _ (C.pairQ_valid P hPmem).2.2
    · exact C.pairQ_passes_r P hPmem
  pairR_count_three := by
    intro P hP
    simp only [HexSawClassification.toEnum_pairBase, HexSawClassification.toEnum_pairLr]
    have hPmem : P ∈ C.pairs := by simpa using hP
    refine hexClass_specialMidCount_three_of_passes _ ?_ ?_ ?_
    · exact C.pairR_passes_p P hPmem
    · exact C.pairR_passes_q P hPmem
    · exact hexClass_endsAt_passesThrough _ _ (C.pairR_valid P hPmem).2.2
  tripQ_not_passes_r := by
    intro T hT
    simp only [HexSawClassification.toEnum_tripBase]
    exact C.tripQ_not_passes_r T (by simpa using hT)
  tripR_not_passes_q := by
    intro T hT
    simp only [HexSawClassification.toEnum_tripBase]
    exact C.tripR_not_passes_q T (by simpa using hT)













theorem hexClass_complete (C : HexSawClassification region a h0 v du) :
    HexVertexComplete C.toEnum where
  complete_p := by
    intro ts hts hp
    obtain ⟨T, hT, hbase⟩ := C.classify_p ts hts hp
    exact ⟨T, by simpa using hT, hbase⟩
  complete_q := by
    intro ts hts hq
    rcases C.classify_q ts hts hq with ⟨T, hT, hext⟩ | ⟨P, hP, hwalk⟩
    · exact Or.inl ⟨T, by simpa using hT, hext⟩
    · exact Or.inr ⟨P, by simpa using hP, hwalk⟩
  complete_r := by
    intro ts hts hr
    rcases C.classify_r ts hts hr with ⟨T, hT, hext⟩ | ⟨P, hP, hwalk⟩
    · exact Or.inl ⟨T, by simpa using hT, hext⟩
    · exact Or.inr ⟨P, by simpa using hP, hwalk⟩

























theorem hexClass_vertex_relation (C : HexSawClassification region a h0 v du)
    (hdu : du ≠ 0)
    (hp : Summable fun ts => parafSummand region a h0 (v + du) (5/8) hexChi ts)
    (hq : Summable fun ts => parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi ts)
    (hr : Summable fun ts => parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts) :
    ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 :=
  relation_of_complete C.toEnum hdu hp hq hr
    C.tripBase_inj C.pairQ_inj C.pairR_inj
    (hexSep_hqcross C.toEnum (hexClass_separated C))
    (hexSep_hrcross C.toEnum (hexClass_separated C))
    (hexClass_complete C)




















def singleTriplet (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (v du : ℂ) (tb : List ℤ)
    (hp : (ofTurns a h0 tb).IsLegalSAW ∧ (ofTurns a h0 tb).StaysIn region
        ∧ (ofTurns a h0 tb).EndsAt (v + du))
    (hq : (ofTurns a h0 (tb ++ [-1])).IsLegalSAW
        ∧ (ofTurns a h0 (tb ++ [-1])).StaysIn region
        ∧ (ofTurns a h0 (tb ++ [-1])).EndsAt (v + hexOmega * du))
    (hr : (ofTurns a h0 (tb ++ [1])).IsLegalSAW
        ∧ (ofTurns a h0 (tb ++ [1])).StaysIn region
        ∧ (ofTurns a h0 (tb ++ [1])).EndsAt (v + hexOmega ^ 2 * du))
    (hQr : ¬ PassesThrough a h0 (tb ++ [-1]) (v + hexOmega ^ 2 * du))
    (hRq : ¬ PassesThrough a h0 (tb ++ [1]) (v + hexOmega * du))
    (hcp : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + du) → tb = ts)
    (hcq : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + hexOmega * du) → tb ++ [-1] = ts)
    (hcr : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) → tb ++ [1] = ts)
    (hreindex :
      (((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
        + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
        + ((v + hexOmega ^ 2 * du) - v) * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi)
      = ((v + du) - v) * parafSummand region a h0 (v + du) (5/8) hexChi tb
          + ((v + hexOmega * du) - v)
              * parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi (tb ++ [-1])
          + ((v + hexOmega ^ 2 * du) - v)
              * parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi (tb ++ [1])) :
    HexSawClassification region a h0 v du where
  pairs := ∅
  pairBase := fun _ => []
  pairLq := fun _ => []
  pairLr := fun _ => []
  pairLq_sum := by simp
  pairLr_sum := by simp
  pairLen := by simp
  pairQ_valid := by simp
  pairR_valid := by simp
  pairQ_passes_p := by simp
  pairQ_passes_r := by simp
  pairR_passes_p := by simp
  pairR_passes_q := by simp
  triplets := {0}
  tripBase := fun _ => tb
  tripP_valid := fun _ _ => hp
  tripQ_valid := fun _ _ => hq
  tripR_valid := fun _ _ => hr
  tripQ_not_passes_r := fun _ _ => hQr
  tripR_not_passes_q := fun _ _ => hRq
  tripBase_inj := by
    rintro ⟨T1, hT1⟩ ⟨T2, hT2⟩ _
    simp only [Finset.mem_singleton] at hT1 hT2
    subst hT1; subst hT2; rfl
  pairQ_inj := by rintro ⟨P1, hP1⟩; exact absurd hP1 (by simp)
  pairR_inj := by rintro ⟨P1, hP1⟩; exact absurd hP1 (by simp)
  classify_p := fun ts hts hend => ⟨0, by simp, hcp ts hts hend⟩
  classify_q := fun ts hts hend => Or.inl ⟨0, by simp, hcq ts hts hend⟩
  classify_r := fun ts hts hend => Or.inl ⟨0, by simp, hcr ts hts hend⟩
  reindex := by
    rw [hreindex]
    rw [Finset.sum_empty, Finset.sum_singleton]
    ring






theorem hexClass_vertex_relation_singleTriplet (region : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (tb : List ℤ) (hdu : du ≠ 0)
    (hp0 : Summable fun ts => parafSummand region a h0 (v + du) (5/8) hexChi ts)
    (hq0 : Summable fun ts => parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi ts)
    (hr0 : Summable fun ts => parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts)
    (hp : (ofTurns a h0 tb).IsLegalSAW ∧ (ofTurns a h0 tb).StaysIn region
        ∧ (ofTurns a h0 tb).EndsAt (v + du))
    (hq : (ofTurns a h0 (tb ++ [-1])).IsLegalSAW
        ∧ (ofTurns a h0 (tb ++ [-1])).StaysIn region
        ∧ (ofTurns a h0 (tb ++ [-1])).EndsAt (v + hexOmega * du))
    (hr : (ofTurns a h0 (tb ++ [1])).IsLegalSAW
        ∧ (ofTurns a h0 (tb ++ [1])).StaysIn region
        ∧ (ofTurns a h0 (tb ++ [1])).EndsAt (v + hexOmega ^ 2 * du))
    (hQr : ¬ PassesThrough a h0 (tb ++ [-1]) (v + hexOmega ^ 2 * du))
    (hRq : ¬ PassesThrough a h0 (tb ++ [1]) (v + hexOmega * du))
    (hcp : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + du) → tb = ts)
    (hcq : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + hexOmega * du) → tb ++ [-1] = ts)
    (hcr : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) → tb ++ [1] = ts)
    (hreindex :
      (((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
        + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
        + ((v + hexOmega ^ 2 * du) - v) * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi)
      = ((v + du) - v) * parafSummand region a h0 (v + du) (5/8) hexChi tb
          + ((v + hexOmega * du) - v)
              * parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi (tb ++ [-1])
          + ((v + hexOmega ^ 2 * du) - v)
              * parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi (tb ++ [1])) :
    ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 :=
  hexClass_vertex_relation
    (singleTriplet region a h0 v du tb hp hq hr hQr hRq hcp hcq hcr hreindex)
    hdu hp0 hq0 hr0

end StatMech.Universality

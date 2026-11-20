/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































































































import Code.Universality.HexFiniteRegion
import Code.Universality.HexVertexClassification

namespace StatMech.Universality

open Complex
open Function
open HexWalk
open scoped BigOperators

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}

















theorem hexPairing_loopReverse_pairs (Lq : List ℤ) (hLqsum : Lq.sum = -4) :
    (loopReverse Lq).sum = 4 ∧ (loopReverse Lq).length = Lq.length
      ∧ loopReverse (loopReverse Lq) = Lq := by
  refine ⟨?_, loopReverse_length Lq, loopReverse_involutive Lq⟩
  rw [loopReverse_sum, hLqsum]; ring




theorem hexPairing_loopReverse_legal (Lq : List ℤ)
    (hLq : ∀ t ∈ Lq, t = 1 ∨ t = -1) :
    ∀ t ∈ loopReverse Lq, t = 1 ∨ t = -1 :=
  loopReverse_legal Lq hLq







theorem hexPairing_pair_walks_ne (base Lq : List ℤ) (hLqsum : Lq.sum = -4) :
    base ++ Lq ≠ base ++ loopReverse Lq := by
  intro h
  have hcancel : Lq = loopReverse Lq := List.append_cancel_left h
  have h1 : (loopReverse Lq).sum = -4 := by rw [← hcancel]; exact hLqsum
  have h2 : (loopReverse Lq).sum = 4 := by rw [loopReverse_sum, hLqsum]; ring
  rw [h1] at h2; norm_num at h2








theorem hexPairing_pair_involution (base Lq : List ℤ) (hLqsum : Lq.sum = -4) :
    loopReverse (loopReverse Lq) = Lq
      ∧ base ++ Lq ≠ base ++ loopReverse Lq
      ∧ (loopReverse Lq).sum = 4 ∧ (loopReverse Lq).length = Lq.length :=
  ⟨loopReverse_involutive Lq, hexPairing_pair_walks_ne base Lq hLqsum,
    (hexPairing_loopReverse_pairs Lq hLqsum).1, (hexPairing_loopReverse_pairs Lq hLqsum).2.1⟩

namespace HexFiniteRegion

variable (R : HexFiniteRegion)
















theorem classify_p_of_supportFinset_covering (hdu : du ≠ 0)
    (triplets : Finset ℕ) (tripBase : ℕ → List ℤ)
    (covp : ∀ ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu,
      (ofTurns a h0 ts).EndsAt (v + du) → ∃ T ∈ triplets, tripBase T = ts) :
    ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du),
      (ofTurns a h0 ts).EndsAt (v + du) →
      ∃ T : ℕ, T ∈ triplets ∧ tripBase T = ts := by
  apply R.classify_p_from_covering triplets tripBase
  intro ts hts hp
  exact covp ts ((R.mem_supportFinset hdu ts).mpr hts) hp




theorem classify_q_of_supportFinset_covering (hdu : du ≠ 0)
    (pairs triplets : Finset ℕ) (pairBase pairLq tripBase : ℕ → List ℤ)
    (covq : ∀ ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu,
      (ofTurns a h0 ts).EndsAt (v + hexOmega * du) →
      (∃ T ∈ triplets, tripBase T ++ [-1] = ts)
        ∨ (∃ P ∈ pairs, pairBase P ++ pairLq P = ts)) :
    ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du),
      (ofTurns a h0 ts).EndsAt (v + hexOmega * du) →
      (∃ T : ℕ, T ∈ triplets ∧ tripBase T ++ [-1] = ts)
        ∨ (∃ P : ℕ, P ∈ pairs ∧ pairBase P ++ pairLq P = ts) := by
  apply R.classify_q_from_covering pairs triplets pairBase pairLq tripBase
  intro ts hts hq
  exact covq ts ((R.mem_supportFinset hdu ts).mpr hts) hq




theorem classify_r_of_supportFinset_covering (hdu : du ≠ 0)
    (pairs triplets : Finset ℕ) (pairBase pairLr tripBase : ℕ → List ℤ)
    (covr : ∀ ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu,
      (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) →
      (∃ T ∈ triplets, tripBase T ++ [1] = ts)
        ∨ (∃ P ∈ pairs, pairBase P ++ pairLr P = ts)) :
    ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du),
      (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) →
      (∃ T : ℕ, T ∈ triplets ∧ tripBase T ++ [1] = ts)
        ∨ (∃ P : ℕ, P ∈ pairs ∧ pairBase P ++ pairLr P = ts) := by
  apply R.classify_r_from_covering pairs triplets pairBase pairLr tripBase
  intro ts hts hr
  exact covr ts ((R.mem_supportFinset hdu ts).mpr hts) hr

end HexFiniteRegion





























noncomputable def hexPairing_classification_of_finiteCovering (R : HexFiniteRegion) (hdu : du ≠ 0)
    (pairs triplets : Finset ℕ)
    (pairBase pairLq pairLr tripBase : ℕ → List ℤ)
    (pairLq_sum : ∀ P ∈ pairs, (pairLq P).sum = -4)
    (pairLr_sum : ∀ P ∈ pairs, (pairLr P).sum = 4)
    (pairLen : ∀ P ∈ pairs, (pairLq P).length = (pairLr P).length)
    (pairQ_valid : ∀ P ∈ pairs,
      (ofTurns a h0 (pairBase P ++ pairLq P)).IsLegalSAW
        ∧ (ofTurns a h0 (pairBase P ++ pairLq P)).StaysIn R.inRegion
        ∧ (ofTurns a h0 (pairBase P ++ pairLq P)).EndsAt (v + hexOmega * du))
    (pairR_valid : ∀ P ∈ pairs,
      (ofTurns a h0 (pairBase P ++ pairLr P)).IsLegalSAW
        ∧ (ofTurns a h0 (pairBase P ++ pairLr P)).StaysIn R.inRegion
        ∧ (ofTurns a h0 (pairBase P ++ pairLr P)).EndsAt (v + hexOmega ^ 2 * du))
    (pairQ_passes_p : ∀ P ∈ pairs, PassesThrough a h0 (pairBase P ++ pairLq P) (v + du))
    (pairQ_passes_r : ∀ P ∈ pairs,
      PassesThrough a h0 (pairBase P ++ pairLq P) (v + hexOmega ^ 2 * du))
    (pairR_passes_p : ∀ P ∈ pairs, PassesThrough a h0 (pairBase P ++ pairLr P) (v + du))
    (pairR_passes_q : ∀ P ∈ pairs,
      PassesThrough a h0 (pairBase P ++ pairLr P) (v + hexOmega * du))
    (tripP_valid : ∀ T ∈ triplets,
      (ofTurns a h0 (tripBase T)).IsLegalSAW
        ∧ (ofTurns a h0 (tripBase T)).StaysIn R.inRegion
        ∧ (ofTurns a h0 (tripBase T)).EndsAt (v + du))
    (tripQ_valid : ∀ T ∈ triplets,
      (ofTurns a h0 (tripBase T ++ [-1])).IsLegalSAW
        ∧ (ofTurns a h0 (tripBase T ++ [-1])).StaysIn R.inRegion
        ∧ (ofTurns a h0 (tripBase T ++ [-1])).EndsAt (v + hexOmega * du))
    (tripR_valid : ∀ T ∈ triplets,
      (ofTurns a h0 (tripBase T ++ [1])).IsLegalSAW
        ∧ (ofTurns a h0 (tripBase T ++ [1])).StaysIn R.inRegion
        ∧ (ofTurns a h0 (tripBase T ++ [1])).EndsAt (v + hexOmega ^ 2 * du))
    (tripQ_not_passes_r : ∀ T ∈ triplets,
      ¬ PassesThrough a h0 (tripBase T ++ [-1]) (v + hexOmega ^ 2 * du))
    (tripR_not_passes_q : ∀ T ∈ triplets,
      ¬ PassesThrough a h0 (tripBase T ++ [1]) (v + hexOmega * du))
    (tripBase_inj : ∀ T1 T2 : triplets, tripBase T1 = tripBase T2 → T1 = T2)
    (pairQ_inj : ∀ P1 P2 : pairs,
      pairBase P1 ++ pairLq P1 = pairBase P2 ++ pairLq P2 → P1 = P2)
    (pairR_inj : ∀ P1 P2 : pairs,
      pairBase P1 ++ pairLr P1 = pairBase P2 ++ pairLr P2 → P1 = P2)
    (covp : ∀ ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu,
      (ofTurns a h0 ts).EndsAt (v + du) → ∃ T ∈ triplets, tripBase T = ts)
    (covq : ∀ ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu,
      (ofTurns a h0 ts).EndsAt (v + hexOmega * du) →
      (∃ T ∈ triplets, tripBase T ++ [-1] = ts)
        ∨ (∃ P ∈ pairs, pairBase P ++ pairLq P = ts))
    (covr : ∀ ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu,
      (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) →
      (∃ T ∈ triplets, tripBase T ++ [1] = ts)
        ∨ (∃ P ∈ pairs, pairBase P ++ pairLr P = ts))
    (reindex :
      (((v + du) - v) * parafObservable R.inRegion a h0 (v + du) (5/8) hexChi
        + ((v + hexOmega * du) - v) * parafObservable R.inRegion a h0 (v + hexOmega * du) (5/8) hexChi
        + ((v + hexOmega ^ 2 * du) - v) * parafObservable R.inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi)
      = (∑ P ∈ pairs,
          (((v + hexOmega * du) - v)
              * parafSummand R.inRegion a h0 (v + hexOmega * du) (5/8) hexChi (pairBase P ++ pairLq P)
            + ((v + hexOmega ^ 2 * du) - v)
                * parafSummand R.inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi (pairBase P ++ pairLr P)))
        + (∑ T ∈ triplets,
            (((v + du) - v) * parafSummand R.inRegion a h0 (v + du) (5/8) hexChi (tripBase T)
              + ((v + hexOmega * du) - v)
                  * parafSummand R.inRegion a h0 (v + hexOmega * du) (5/8) hexChi (tripBase T ++ [-1])
              + ((v + hexOmega ^ 2 * du) - v)
                  * parafSummand R.inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi (tripBase T ++ [1])))) :
    HexSawClassification R.inRegion a h0 v du where
  pairs := pairs
  pairBase := pairBase
  pairLq := pairLq
  pairLr := pairLr
  pairLq_sum := pairLq_sum
  pairLr_sum := pairLr_sum
  pairLen := pairLen
  pairQ_valid := pairQ_valid
  pairR_valid := pairR_valid
  pairQ_passes_p := pairQ_passes_p
  pairQ_passes_r := pairQ_passes_r
  pairR_passes_p := pairR_passes_p
  pairR_passes_q := pairR_passes_q
  triplets := triplets
  tripBase := tripBase
  tripP_valid := tripP_valid
  tripQ_valid := tripQ_valid
  tripR_valid := tripR_valid
  tripQ_not_passes_r := tripQ_not_passes_r
  tripR_not_passes_q := tripR_not_passes_q
  tripBase_inj := tripBase_inj
  pairQ_inj := pairQ_inj
  pairR_inj := pairR_inj
  classify_p := R.classify_p_of_supportFinset_covering hdu triplets tripBase covp
  classify_q := R.classify_q_of_supportFinset_covering hdu pairs triplets pairBase pairLq tripBase covq
  classify_r := R.classify_r_of_supportFinset_covering hdu pairs triplets pairBase pairLr tripBase covr
  reindex := reindex





















theorem hexPairing_emptySupport_observable_zero (a w : ℂ) (h0 : ℤ) (z : ℂ) (σ x : ℝ)
    (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) →
      ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
    (haz : a ≠ z) :
    parafObservable (hexFiniteRegion_single a w hclosure).inRegion a h0 z σ x = 0 := by
  have hend0 : (ofTurns a h0 ([] : List ℤ)).endMid = a := trivialWalk_endMid a h0
  unfold parafObservable
  have hfun : (fun ts => parafSummand (hexFiniteRegion_single a w hclosure).inRegion a h0 z σ x ts)
      = (fun _ => (0 : ℂ)) := by
    funext ts
    unfold parafSummand
    rw [if_neg]
    rintro ⟨hlegal, hstay, hend⟩
    have hnil : ts = [] := hexFiniteRegion_single_length a w h0 ts hclosure hlegal.2 hstay
    subst hnil
    rw [HexWalk.EndsAt, hend0] at hend
    exact haz hend
  rw [hfun]; exact tsum_zero






theorem hexPairing_emptySupport (a w : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0)
    (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) →
      ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
    (hap : a ≠ v + du) (haq : a ≠ v + hexOmega * du) (har : a ≠ v + hexOmega ^ 2 * du)
    (ts : List ℤ) :
    ts ∉ Function.support
      (combinedSummand (hexFiniteRegion_single a w hclosure).inRegion a h0 v du) := by
  intro h
  obtain ⟨hlegal, hstay⟩ :=
    (hexFiniteRegion_single a w hclosure).support_isLegalSAW_staysIn hdu ts h
  have hnil : ts = [] :=
    hexFiniteRegion_single_length a w h0 ts hclosure hlegal.2 hstay
  subst hnil
  
  
  have hend : (ofTurns a h0 ([] : List ℤ)).endMid = a := trivialWalk_endMid a h0
  rcases support_endsAt_threeMid (region := (hexFiniteRegion_single a w hclosure).inRegion) [] h
    with hp | hq | hr
  · exact hap (by rw [HexWalk.EndsAt] at hp; rw [← hp, hend])
  · exact haq (by rw [HexWalk.EndsAt] at hq; rw [← hq, hend])
  · exact har (by rw [HexWalk.EndsAt] at hr; rw [← hr, hend])







noncomputable def hexPairing_emptySupport_classification (a w : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0)
    (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) →
      ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
    (hap : a ≠ v + du) (haq : a ≠ v + hexOmega * du) (har : a ≠ v + hexOmega ^ 2 * du) :
    HexSawClassification (hexFiniteRegion_single a w hclosure).inRegion a h0 v du :=
  hexPairing_classification_of_finiteCovering
    (hexFiniteRegion_single a w hclosure) hdu
    (pairs := ∅) (triplets := ∅)
    (pairBase := fun _ => []) (pairLq := fun _ => []) (pairLr := fun _ => [])
    (tripBase := fun _ => [])
    (pairLq_sum := by simp) (pairLr_sum := by simp) (pairLen := by simp)
    (pairQ_valid := by simp) (pairR_valid := by simp)
    (pairQ_passes_p := by simp) (pairQ_passes_r := by simp)
    (pairR_passes_p := by simp) (pairR_passes_q := by simp)
    (tripP_valid := by simp) (tripQ_valid := by simp) (tripR_valid := by simp)
    (tripQ_not_passes_r := by simp) (tripR_not_passes_q := by simp)
    (tripBase_inj := by rintro ⟨T1, hT1⟩; exact absurd hT1 (by simp))
    (pairQ_inj := by rintro ⟨P1, hP1⟩; exact absurd hP1 (by simp))
    (pairR_inj := by rintro ⟨P1, hP1⟩; exact absurd hP1 (by simp))
    (covp := by
      intro ts hts _
      exact absurd ((((hexFiniteRegion_single a w hclosure).mem_supportFinset hdu ts).mp hts))
        (hexPairing_emptySupport a w h0 v du hdu hclosure hap haq har ts))
    (covq := by
      intro ts hts _
      exact absurd ((((hexFiniteRegion_single a w hclosure).mem_supportFinset hdu ts).mp hts))
        (hexPairing_emptySupport a w h0 v du hdu hclosure hap haq har ts))
    (covr := by
      intro ts hts _
      exact absurd ((((hexFiniteRegion_single a w hclosure).mem_supportFinset hdu ts).mp hts))
        (hexPairing_emptySupport a w h0 v du hdu hclosure hap haq har ts))
    (reindex := by
      rw [Finset.sum_empty, Finset.sum_empty, add_zero]
      
      rw [hexPairing_emptySupport_observable_zero a w h0 (v + du) (5/8) hexChi hclosure hap,
          hexPairing_emptySupport_observable_zero a w h0 (v + hexOmega * du) (5/8) hexChi hclosure haq,
          hexPairing_emptySupport_observable_zero a w h0 (v + hexOmega ^ 2 * du) (5/8) hexChi hclosure har]
      ring)
















theorem hexPairing_vertex_relation_of_classification (R : HexFiniteRegion)
    (C : HexSawClassification R.inRegion a h0 v du) (hdu : du ≠ 0)
    (hp : Summable fun ts => parafSummand R.inRegion a h0 (v + du) (5/8) hexChi ts)
    (hq : Summable fun ts => parafSummand R.inRegion a h0 (v + hexOmega * du) (5/8) hexChi ts)
    (hr : Summable fun ts => parafSummand R.inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts) :
    ((v + du) - v) * parafObservable R.inRegion a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable R.inRegion a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable R.inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 :=
  hexClass_vertex_relation C hdu hp hq hr











theorem hexPairing_emptySupport_summand_zero (a w : ℂ) (h0 : ℤ) (z : ℂ) (σ x : ℝ)
    (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) →
      ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
    (haz : a ≠ z) (ts : List ℤ) :
    parafSummand (hexFiniteRegion_single a w hclosure).inRegion a h0 z σ x ts = 0 := by
  have hend0 : (ofTurns a h0 ([] : List ℤ)).endMid = a := trivialWalk_endMid a h0
  unfold parafSummand
  rw [if_neg]
  rintro ⟨hlegal, hstay, hend⟩
  have hnil : ts = [] := hexFiniteRegion_single_length a w h0 ts hclosure hlegal.2 hstay
  subst hnil
  rw [HexWalk.EndsAt, hend0] at hend
  exact haz hend


theorem hexPairing_emptySupport_summable (a w : ℂ) (h0 : ℤ) (z : ℂ) (σ x : ℝ)
    (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) →
      ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
    (haz : a ≠ z) :
    Summable fun ts => parafSummand (hexFiniteRegion_single a w hclosure).inRegion a h0 z σ x ts := by
  rw [show (fun ts => parafSummand (hexFiniteRegion_single a w hclosure).inRegion a h0 z σ x ts)
        = (fun _ => (0 : ℂ)) from
      funext fun ts => hexPairing_emptySupport_summand_zero a w h0 z σ x hclosure haz ts]
  exact summable_zero








theorem hexPairing_emptySupport_vertex_relation (a w : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0)
    (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) →
      ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
    (hap : a ≠ v + du) (haq : a ≠ v + hexOmega * du) (har : a ≠ v + hexOmega ^ 2 * du) :
    ((v + du) - v)
        * parafObservable (hexFiniteRegion_single a w hclosure).inRegion a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v)
          * parafObservable (hexFiniteRegion_single a w hclosure).inRegion a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable (hexFiniteRegion_single a w hclosure).inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi
      = 0 :=
  hexPairing_vertex_relation_of_classification
    (hexFiniteRegion_single a w hclosure)
    (hexPairing_emptySupport_classification a w h0 v du hdu hclosure hap haq har) hdu
    (hexPairing_emptySupport_summable a w h0 (v + du) (5/8) hexChi hclosure hap)
    (hexPairing_emptySupport_summable a w h0 (v + hexOmega * du) (5/8) hexChi hclosure haq)
    (hexPairing_emptySupport_summable a w h0 (v + hexOmega ^ 2 * du) (5/8) hexChi hclosure har)















theorem hexPairing_covering (a w : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0)
    (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) →
      ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
    (hap : a ≠ v + du) (haq : a ≠ v + hexOmega * du) (har : a ≠ v + hexOmega ^ 2 * du) :
    (∀ ts ∈ (hexFiniteRegion_single a w hclosure).supportFinset
          (a := a) (h0 := h0) (v := v) (du := du) hdu,
        (ofTurns a h0 ts).EndsAt (v + du) →
        ∃ T ∈ (∅ : Finset ℕ), (fun _ : ℕ => ([] : List ℤ)) T = ts)
      ∧ (∀ ts ∈ (hexFiniteRegion_single a w hclosure).supportFinset
            (a := a) (h0 := h0) (v := v) (du := du) hdu,
          (ofTurns a h0 ts).EndsAt (v + hexOmega * du) →
          (∃ T ∈ (∅ : Finset ℕ), (fun _ : ℕ => ([] : List ℤ)) T ++ [-1] = ts)
            ∨ (∃ P ∈ (∅ : Finset ℕ),
                (fun _ : ℕ => ([] : List ℤ)) P ++ (fun _ : ℕ => ([] : List ℤ)) P = ts))
      ∧ (∀ ts ∈ (hexFiniteRegion_single a w hclosure).supportFinset
            (a := a) (h0 := h0) (v := v) (du := du) hdu,
          (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) →
          (∃ T ∈ (∅ : Finset ℕ), (fun _ : ℕ => ([] : List ℤ)) T ++ [1] = ts)
            ∨ (∃ P ∈ (∅ : Finset ℕ),
                (fun _ : ℕ => ([] : List ℤ)) P ++ (fun _ : ℕ => ([] : List ℤ)) P = ts)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · intro ts hts _
    exact absurd ((((hexFiniteRegion_single a w hclosure).mem_supportFinset hdu ts).mp hts))
      (hexPairing_emptySupport a w h0 v du hdu hclosure hap haq har ts)





noncomputable def hexPairing_classification (a w : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0)
    (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) →
      ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
    (hap : a ≠ v + du) (haq : a ≠ v + hexOmega * du) (har : a ≠ v + hexOmega ^ 2 * du) :
    HexSawClassification (hexFiniteRegion_single a w hclosure).inRegion a h0 v du :=
  hexPairing_emptySupport_classification a w h0 v du hdu hclosure hap haq har





theorem hexPairing_vertex_relation (a w : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0)
    (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) →
      ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
    (hap : a ≠ v + du) (haq : a ≠ v + hexOmega * du) (har : a ≠ v + hexOmega ^ 2 * du) :
    ((v + du) - v)
        * parafObservable (hexFiniteRegion_single a w hclosure).inRegion a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v)
          * parafObservable (hexFiniteRegion_single a w hclosure).inRegion a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable (hexFiniteRegion_single a w hclosure).inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi
      = 0 :=
  hexPairing_emptySupport_vertex_relation a w h0 v du hdu hclosure hap haq har

end StatMech.Universality


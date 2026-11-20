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

namespace StatMech.Universality

open Complex
open Function
open HexWalk

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}





























structure HexVertexComplete (E : HexVertexEnumeration region a h0 v du) : Prop where
  

  complete_p : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
    (ofTurns a h0 ts).EndsAt (v + du) →
    ∃ T : ℕ, T ∈ E.triplets ∧ E.tripBase T = ts
  


  complete_q : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
    (ofTurns a h0 ts).EndsAt (v + hexOmega * du) →
    (∃ T : ℕ, T ∈ E.triplets ∧ E.tripBase T ++ [-1] = ts)
      ∨ (∃ P : ℕ, P ∈ E.pairs ∧ E.pairBase P ++ E.pairLq P = ts)
  


  complete_r : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
    (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) →
    (∃ T : ℕ, T ∈ E.triplets ∧ E.tripBase T ++ [1] = ts)
      ∨ (∃ P : ℕ, P ∈ E.pairs ∧ E.pairBase P ++ E.pairLr P = ts)






















theorem hexCov_covp (E : HexVertexEnumeration region a h0 v du)
    (hC : HexVertexComplete E) :
    ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
      (ofTurns a h0 ts).EndsAt (v + du) →
      ∃ slot : SlotType E, E.slotTurns slot = ts := by
  intro ts hts hp
  obtain ⟨T, hT, hbase⟩ := hC.complete_p ts hts hp
  refine ⟨Sum.inr (⟨T, hT⟩, (0 : Fin 3)), ?_⟩
  show E.tripBase T = ts
  exact hbase






theorem hexCov_covq (E : HexVertexEnumeration region a h0 v du)
    (hC : HexVertexComplete E) :
    ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
      (ofTurns a h0 ts).EndsAt (v + hexOmega * du) →
      ∃ slot : SlotType E, E.slotTurns slot = ts := by
  intro ts hts hq
  rcases hC.complete_q ts hts hq with ⟨T, hT, hext⟩ | ⟨P, hP, hwalk⟩
  · refine ⟨Sum.inr (⟨T, hT⟩, (1 : Fin 3)), ?_⟩
    show E.tripBase T ++ [-1] = ts
    exact hext
  · refine ⟨Sum.inl (⟨P, hP⟩, false), ?_⟩
    show E.pairBase P ++ E.pairLq P = ts
    exact hwalk






theorem hexCov_covr (E : HexVertexEnumeration region a h0 v du)
    (hC : HexVertexComplete E) :
    ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
      (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) →
      ∃ slot : SlotType E, E.slotTurns slot = ts := by
  intro ts hts hr
  rcases hC.complete_r ts hts hr with ⟨T, hT, hext⟩ | ⟨P, hP, hwalk⟩
  · refine ⟨Sum.inr (⟨T, hT⟩, (2 : Fin 3)), ?_⟩
    show E.tripBase T ++ [1] = ts
    exact hext
  · refine ⟨Sum.inl (⟨P, hP⟩, true), ?_⟩
    show E.pairBase P ++ E.pairLr P = ts
    exact hwalk








theorem hsub_from_coverage_proved (E : HexVertexEnumeration region a h0 v du)
    (hC : HexVertexComplete E) :
    Function.support (combinedSummand region a h0 v du) ⊆
      Set.range fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) =>
        E.slotTurns x.1 :=
  hsub_of_coverage E (hexCov_covp E hC) (hexCov_covq E hC) (hexCov_covr E hC)















theorem relation_of_complete (E : HexVertexEnumeration region a h0 v du)
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
    (hC : HexVertexComplete E) :
    ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 :=
  HexVertexEnumeration.relation_of_bijection E hdu hp hq hr
    (hinj_general E hdu htinj hqinj hrinj hqcross hrcross)
    (hsub_from_coverage_proved E hC)












theorem complete_emptyRegion (a : ℂ) (h0 : ℤ) (v du : ℂ) :
    HexVertexComplete (emptyEnumeration a h0 v du) where
  complete_p := fun ts hts _ =>
    absurd (combinedSummand_emptyRegion a h0 v du ts) hts
  complete_q := fun ts hts _ =>
    absurd (combinedSummand_emptyRegion a h0 v du ts) hts
  complete_r := fun ts hts _ =>
    absurd (combinedSummand_emptyRegion a h0 v du ts) hts







theorem relation_complete_emptyRegion (a : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0) :
    ((v + du) - v) * parafObservable (fun _ => False) a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v)
          * parafObservable (fun _ => False) a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable (fun _ => False) a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 :=
  relation_of_complete (emptyEnumeration a h0 v du) hdu
    (summable_emptyRegion a h0 _ _ _) (summable_emptyRegion a h0 _ _ _)
    (summable_emptyRegion a h0 _ _ _)
    (fun T1 _ _ => absurd T1.2 (Finset.notMem_empty _))
    (fun P1 _ _ => absurd P1.2 (Finset.notMem_empty _))
    (fun P1 _ _ => absurd P1.2 (Finset.notMem_empty _))
    (fun P _ => absurd P.2 (Finset.notMem_empty _))
    (fun P _ => absurd P.2 (Finset.notMem_empty _))
    (complete_emptyRegion a h0 v du)

end StatMech.Universality

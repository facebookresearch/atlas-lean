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












def PassesThrough (a : ℂ) (h0 : ℤ) (ts : List ℤ) (z : ℂ) : Prop :=
  z ∈ (ofTurns a h0 ts).mids



theorem hexSep_passesThrough_congr (a : ℂ) (h0 : ℤ) (ts ts' : List ℤ) (z : ℂ)
    (h : ts = ts') : PassesThrough a h0 ts z ↔ PassesThrough a h0 ts' z := by
  rw [h]

open Classical in





noncomputable def specialMidCount (a : ℂ) (h0 : ℤ) (v du : ℂ) (ts : List ℤ) : ℕ :=
  (if PassesThrough a h0 ts (v + du) then 1 else 0)
    + (if PassesThrough a h0 ts (v + hexOmega * du) then 1 else 0)
    + (if PassesThrough a h0 ts (v + hexOmega ^ 2 * du) then 1 else 0)


theorem hexSep_specialMidCount_congr (a : ℂ) (h0 : ℤ) (v du : ℂ) (ts ts' : List ℤ)
    (h : ts = ts') :
    specialMidCount a h0 v du ts = specialMidCount a h0 v du ts' := by
  rw [h]





theorem hexSep_passesThrough_r_of_count_three (ts : List ℤ)
    (hk : specialMidCount a h0 v du ts = 3) :
    PassesThrough a h0 ts (v + hexOmega ^ 2 * du) := by
  classical
  unfold specialMidCount at hk
  by_contra hc
  rw [if_neg hc] at hk
  have h1 : (if PassesThrough a h0 ts (v + du) then (1 : ℕ) else 0) ≤ 1 := by
    split <;> norm_num
  have h2 : (if PassesThrough a h0 ts (v + hexOmega * du) then (1 : ℕ) else 0) ≤ 1 := by
    split <;> norm_num
  omega





theorem hexSep_passesThrough_q_of_count_three (ts : List ℤ)
    (hk : specialMidCount a h0 v du ts = 3) :
    PassesThrough a h0 ts (v + hexOmega * du) := by
  classical
  unfold specialMidCount at hk
  by_contra hc
  rw [if_neg hc] at hk
  have h1 : (if PassesThrough a h0 ts (v + du) then (1 : ℕ) else 0) ≤ 1 := by
    split <;> norm_num
  have h3 : (if PassesThrough a h0 ts (v + hexOmega ^ 2 * du) then (1 : ℕ) else 0) ≤ 1 := by
    split <;> norm_num
  omega












theorem hexSep_neg_len_le_sum (L : List ℤ) (hL : ∀ t ∈ L, t = 1 ∨ t = -1) :
    -(L.length : ℤ) ≤ L.sum := by
  induction L with
  | nil => simp
  | cons y ys ih =>
    have hy : y = 1 ∨ y = -1 := hL y (by simp)
    have hys : ∀ t ∈ ys, t = 1 ∨ t = -1 := fun t ht => hL t (by simp [ht])
    have hb := ih hys
    simp only [List.length_cons, List.sum_cons]
    push_cast; rcases hy with h | h <;> omega





theorem hexSep_legalSum_neg_four_len_ge (L : List ℤ) (hL : ∀ t ∈ L, t = 1 ∨ t = -1)
    (hsum : L.sum = -4) : 4 ≤ L.length := by
  have hb := hexSep_neg_len_le_sum L hL
  rw [hsum] at hb
  have : (4 : ℤ) ≤ (L.length : ℤ) := by omega
  exact_mod_cast this





theorem hexSep_pairLq_length_ge (E : HexVertexEnumeration region a h0 v du)
    (P : ℕ) (hP : P ∈ E.pairs) : 4 ≤ (E.pairLq P).length := by
  have hlegal := (E.pairQ_valid P hP).1.1
  unfold HexWalk.LegalTurns at hlegal
  simp only [ofTurns_turns] at hlegal
  exact hexSep_legalSum_neg_four_len_ge (E.pairLq P)
    (fun t ht => hlegal t (by simp [ht]))
    (E.pairLq_sum P hP)





























structure HexVertexSeparated (E : HexVertexEnumeration region a h0 v du) : Prop where
  

  pairQ_count_three : ∀ P ∈ E.pairs,
    specialMidCount a h0 v du (E.pairBase P ++ E.pairLq P) = 3
  

  pairR_count_three : ∀ P ∈ E.pairs,
    specialMidCount a h0 v du (E.pairBase P ++ E.pairLr P) = 3
  

  tripQ_not_passes_r : ∀ T ∈ E.triplets,
    ¬ PassesThrough a h0 (E.tripBase T ++ [-1]) (v + hexOmega ^ 2 * du)
  

  tripR_not_passes_q : ∀ T ∈ E.triplets,
    ¬ PassesThrough a h0 (E.tripBase T ++ [1]) (v + hexOmega * du)













theorem hexSep_hqcross (E : HexVertexEnumeration region a h0 v du)
    (hS : HexVertexSeparated E) :
    ∀ (P : E.pairs) (T : E.triplets),
      E.pairBase P ++ E.pairLq P ≠ E.tripBase T ++ [-1] := by
  rintro ⟨P, hP⟩ ⟨T, hT⟩ heq
  have h1 : PassesThrough a h0 (E.pairBase P ++ E.pairLq P) (v + hexOmega ^ 2 * du) :=
    hexSep_passesThrough_r_of_count_three _ (hS.pairQ_count_three P hP)
  rw [heq] at h1
  exact hS.tripQ_not_passes_r T hT h1






theorem hexSep_hrcross (E : HexVertexEnumeration region a h0 v du)
    (hS : HexVertexSeparated E) :
    ∀ (P : E.pairs) (T : E.triplets),
      E.pairBase P ++ E.pairLr P ≠ E.tripBase T ++ [1] := by
  rintro ⟨P, hP⟩ ⟨T, hT⟩ heq
  have h1 : PassesThrough a h0 (E.pairBase P ++ E.pairLr P) (v + hexOmega * du) :=
    hexSep_passesThrough_q_of_count_three _ (hS.pairR_count_three P hP)
  rw [heq] at h1
  exact hS.tripR_not_passes_q T hT h1














theorem hexSep_hinj (E : HexVertexEnumeration region a h0 v du) (hdu : du ≠ 0)
    (htinj : ∀ T1 T2 : E.triplets, E.tripBase T1 = E.tripBase T2 → T1 = T2)
    (hqinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLq P1 = E.pairBase P2 ++ E.pairLq P2 → P1 = P2)
    (hrinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLr P1 = E.pairBase P2 ++ E.pairLr P2 → P1 = P2)
    (hS : HexVertexSeparated E) :
    Function.Injective
      fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) =>
        E.slotTurns x.1 :=
  hinj_general E hdu htinj hqinj hrinj (hexSep_hqcross E hS) (hexSep_hrcross E hS)


















theorem hexSep_relation (E : HexVertexEnumeration region a h0 v du)
    (hdu : du ≠ 0)
    (hp : Summable fun ts => parafSummand region a h0 (v + du) (5/8) hexChi ts)
    (hq : Summable fun ts => parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi ts)
    (hr : Summable fun ts => parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts)
    (htinj : ∀ T1 T2 : E.triplets, E.tripBase T1 = E.tripBase T2 → T1 = T2)
    (hqinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLq P1 = E.pairBase P2 ++ E.pairLq P2 → P1 = P2)
    (hrinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLr P1 = E.pairBase P2 ++ E.pairLr P2 → P1 = P2)
    (hS : HexVertexSeparated E)
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
    (hexSep_hinj E hdu htinj hqinj hrinj hS)
    (hsub_of_coverage E covp covq covr)












theorem hexSep_separated_empty (a : ℂ) (h0 : ℤ) (v du : ℂ)
    (hzero : ∀ z, parafObservable (fun _ => False) a h0 z (5/8) hexChi = 0) :
    HexVertexSeparated (HexVertexEnumeration.empty (fun _ => False) a h0 v du hzero) where
  pairQ_count_three := by
    intro P hP; exact absurd hP (by simp [HexVertexEnumeration.empty])
  pairR_count_three := by
    intro P hP; exact absurd hP (by simp [HexVertexEnumeration.empty])
  tripQ_not_passes_r := by
    intro T hT; exact absurd hT (by simp [HexVertexEnumeration.empty])
  tripR_not_passes_q := by
    intro T hT; exact absurd hT (by simp [HexVertexEnumeration.empty])

end StatMech.Universality

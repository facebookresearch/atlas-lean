/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.HexLattice
import Code.Universality.HexVertex

namespace StatMech.Universality

open Complex
open HexWalk


theorem hexPhase_eq_lambda_zpow (w : HexWalk) :
    Complex.exp (-Complex.I * ((5/8 : ℝ) : ℂ) * ((w.turning : ℝ) : ℂ))
      = hexLambda ^ (w.turnCount) := by
  unfold hexLambda
  rw [hexExpI_zpow]
  rw [turning]
  congr 1
  push_cast
  ring








theorem hexContribution_eq_paraf (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z v : ℂ)
    (ts : List ℤ)
    (hcond : (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn region
        ∧ (ofTurns a h0 ts).EndsAt z) :
    (z - v) * parafSummand region a h0 z (5/8) hexChi ts
      = hexContribution (z - v) ((ofTurns a h0 ts).turnCount)
          ((ofTurns a h0 ts).numVertices) := by
  unfold parafSummand hexContribution
  rw [if_pos hcond]
  rw [show ((hexChi : ℝ) : ℂ) = (hexChi : ℂ) from rfl]
  rw [← hexPhase_eq_lambda_zpow (ofTurns a h0 ts)]
  ring











theorem numVertices_concat (a : ℂ) (h0 t : ℤ) (ts : List ℤ) :
    (ofTurns a h0 (ts ++ [t])).numVertices = (ofTurns a h0 ts).numVertices + 1 := by
  simp [numVertices, ofTurns]




theorem turnCount_concat (a : ℂ) (h0 t : ℤ) (ts : List ℤ) :
    (ofTurns a h0 (ts ++ [t])).turnCount = (ofTurns a h0 ts).turnCount + t := by
  simp [turnCount, ofTurns, List.sum_append]











theorem turnCount_append_block (a : ℂ) (h0 : ℤ) (base block : List ℤ) :
    (ofTurns a h0 (base ++ block)).turnCount
      = (ofTurns a h0 base).turnCount + block.sum := by
  simp [turnCount, ofTurns, List.sum_append]





theorem hexUnit_add_two (h : ℤ) : hexUnit (h + 2) = hexOmega * hexUnit h := by
  unfold hexUnit hexOmega
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring


theorem hexUnit_add_four (h : ℤ) : hexUnit (h + 4) = hexOmega ^ 2 * hexUnit h := by
  rw [show (h + 4 : ℤ) = (h + 2) + 2 by ring, hexUnit_add_two, hexUnit_add_two]
  ring


















theorem genuine_triplet_zero (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (v du : ℂ)
    (ts : List ℤ)
    (hp : (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn region
        ∧ (ofTurns a h0 ts).EndsAt (v + du))
    (hq : (ofTurns a h0 (ts ++ [-1])).IsLegalSAW
        ∧ (ofTurns a h0 (ts ++ [-1])).StaysIn region
        ∧ (ofTurns a h0 (ts ++ [-1])).EndsAt (v + hexOmega * du))
    (hr : (ofTurns a h0 (ts ++ [1])).IsLegalSAW
        ∧ (ofTurns a h0 (ts ++ [1])).StaysIn region
        ∧ (ofTurns a h0 (ts ++ [1])).EndsAt (v + hexOmega ^ 2 * du)) :
    ((v + du) - v) * parafSummand region a h0 (v + du) (5/8) hexChi ts
      + ((v + hexOmega * du) - v)
          * parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi (ts ++ [-1])
      + ((v + hexOmega ^ 2 * du) - v)
          * parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi (ts ++ [1])
      = 0 := by
  rw [hexContribution_eq_paraf region a h0 (v + du) v ts hp,
      hexContribution_eq_paraf region a h0 (v + hexOmega * du) v (ts ++ [-1]) hq,
      hexContribution_eq_paraf region a h0 (v + hexOmega ^ 2 * du) v (ts ++ [1]) hr]
  
  rw [turnCount_concat a h0 (-1) ts, turnCount_concat a h0 1 ts,
      numVertices_concat a h0 (-1) ts, numVertices_concat a h0 1 ts]
  
  simp only [add_sub_cancel_left]
  
  have key := hexTripletContribution_zero du ((ofTurns a h0 ts).turnCount)
      ((ofTurns a h0 ts).numVertices)
  
  
  have e1 : ((ofTurns a h0 ts).turnCount + (-1 : ℤ)) = (ofTurns a h0 ts).turnCount - 1 := by
    ring
  rw [e1]
  exact key






















theorem genuine_pair_zero (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (v du : ℂ)
    (base Lq Lr : List ℤ)
    (hLqsum : Lq.sum = -4) (hLrsum : Lr.sum = 4)
    (hlen : Lq.length = Lr.length)
    (hq : (ofTurns a h0 (base ++ Lq)).IsLegalSAW
        ∧ (ofTurns a h0 (base ++ Lq)).StaysIn region
        ∧ (ofTurns a h0 (base ++ Lq)).EndsAt (v + hexOmega * du))
    (hr : (ofTurns a h0 (base ++ Lr)).IsLegalSAW
        ∧ (ofTurns a h0 (base ++ Lr)).StaysIn region
        ∧ (ofTurns a h0 (base ++ Lr)).EndsAt (v + hexOmega ^ 2 * du)) :
    ((v + hexOmega * du) - v)
        * parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi (base ++ Lq)
      + ((v + hexOmega ^ 2 * du) - v)
          * parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi (base ++ Lr)
      = 0 := by
  rw [hexContribution_eq_paraf region a h0 (v + hexOmega * du) v (base ++ Lq) hq,
      hexContribution_eq_paraf region a h0 (v + hexOmega ^ 2 * du) v (base ++ Lr) hr]
  
  rw [turnCount_append_block a h0 base Lq, turnCount_append_block a h0 base Lr,
      hLqsum, hLrsum]
  
  have hnq : (ofTurns a h0 (base ++ Lq)).numVertices
      = (ofTurns a h0 base).numVertices + Lq.length := by
    simp only [numVertices, ofTurns, List.length_append]; omega
  have hnr : (ofTurns a h0 (base ++ Lr)).numVertices
      = (ofTurns a h0 base).numVertices + Lr.length := by
    simp only [numVertices, ofTurns, List.length_append]; omega
  rw [hnq, hnr, ← hlen]
  simp only [add_sub_cancel_left]
  
  have key := hexPairContribution_zero du ((ofTurns a h0 base).turnCount)
      ((ofTurns a h0 base).numVertices + Lq.length)
  
  have e1 : ((ofTurns a h0 base).turnCount + (-4 : ℤ))
      = (ofTurns a h0 base).turnCount - 4 := by ring
  rw [e1]
  exact key




















def loopReverse (L : List ℤ) : List ℤ := (L.map (fun t => -t)).reverse



theorem loopReverse_sum (L : List ℤ) : (loopReverse L).sum = - L.sum := by
  unfold loopReverse
  rw [List.sum_reverse]
  induction L with
  | nil => simp
  | cons x xs ih => simp [ih]; ring


@[simp]
theorem loopReverse_length (L : List ℤ) : (loopReverse L).length = L.length := by
  simp [loopReverse]


theorem loopReverse_legal (L : List ℤ) (hL : ∀ t ∈ L, t = 1 ∨ t = -1) :
    ∀ t ∈ loopReverse L, t = 1 ∨ t = -1 := by
  intro t ht
  unfold loopReverse at ht
  rw [List.mem_reverse, List.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  rcases hL s hs with h | h <;> simp [h]



theorem loopReverse_involutive (L : List ℤ) : loopReverse (loopReverse L) = L := by
  unfold loopReverse
  rw [List.map_reverse, List.reverse_reverse, List.map_map]
  simp







theorem genuine_pair_zero_via_reversal (region : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (base Lq : List ℤ) (hLqsum : Lq.sum = -4)
    (hq : (ofTurns a h0 (base ++ Lq)).IsLegalSAW
        ∧ (ofTurns a h0 (base ++ Lq)).StaysIn region
        ∧ (ofTurns a h0 (base ++ Lq)).EndsAt (v + hexOmega * du))
    (hr : (ofTurns a h0 (base ++ loopReverse Lq)).IsLegalSAW
        ∧ (ofTurns a h0 (base ++ loopReverse Lq)).StaysIn region
        ∧ (ofTurns a h0 (base ++ loopReverse Lq)).EndsAt (v + hexOmega ^ 2 * du)) :
    ((v + hexOmega * du) - v)
        * parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi (base ++ Lq)
      + ((v + hexOmega ^ 2 * du) - v)
          * parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi
              (base ++ loopReverse Lq)
      = 0 :=
  genuine_pair_zero region a h0 v du base Lq (loopReverse Lq) hLqsum
    (by rw [loopReverse_sum, hLqsum]; ring) (loopReverse_length Lq).symm hq hr








theorem hexOmega_primRoot : IsPrimitiveRoot hexOmega 3 := by
  have h : hexOmega = Complex.exp (2 * Real.pi * Complex.I / 3) := by
    unfold hexOmega; congr 1; push_cast; ring
  rw [h]; exact Complex.isPrimitiveRoot_exp 3 (by norm_num)

theorem hexOmega_ne_one : hexOmega ≠ 1 := by
  intro h
  have := hexOmega_primRoot.pow_ne_one_of_pos_of_lt (l := 1) (by norm_num) (by norm_num)
  simp at this; exact this h

theorem hexOmega_sq_ne_one : hexOmega ^ 2 ≠ 1 :=
  hexOmega_primRoot.pow_ne_one_of_pos_of_lt (l := 2) (by norm_num) (by norm_num)

theorem hexOmega_ne_sq : hexOmega ≠ hexOmega ^ 2 := by
  intro h
  have hne : hexOmega ≠ 0 := hexOmega_primRoot.ne_zero (by norm_num)
  apply hexOmega_ne_one
  have h2 : hexOmega * hexOmega = hexOmega * 1 := by rw [mul_one, ← sq, ← h]
  exact mul_left_cancel₀ hne h2


theorem hexMid_p_ne_q {v du : ℂ} (hdu : du ≠ 0) : v + du ≠ v + hexOmega * du := by
  intro h
  have : du = hexOmega * du := by linear_combination h
  apply hexOmega_ne_one
  have := mul_right_cancel₀ hdu (by rw [one_mul]; exact this : (1 : ℂ) * du = hexOmega * du)
  exact this.symm


theorem hexMid_p_ne_r {v du : ℂ} (hdu : du ≠ 0) : v + du ≠ v + hexOmega ^ 2 * du := by
  intro h
  have : du = hexOmega ^ 2 * du := by linear_combination h
  apply hexOmega_sq_ne_one
  have := mul_right_cancel₀ hdu (by rw [one_mul]; exact this : (1 : ℂ) * du = hexOmega ^ 2 * du)
  exact this.symm


theorem hexMid_q_ne_r {v du : ℂ} (hdu : du ≠ 0) :
    v + hexOmega * du ≠ v + hexOmega ^ 2 * du := by
  intro h
  have hh : hexOmega * du = hexOmega ^ 2 * du := by linear_combination h
  apply hexOmega_ne_sq
  exact mul_right_cancel₀ hdu hh








theorem parafSummand_eq_zero_of_not_endsAt (region : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (z : ℂ) (σ x : ℝ) (ts : List ℤ) (hne : ¬ (ofTurns a h0 ts).EndsAt z) :
    parafSummand region a h0 z σ x ts = 0 := by
  unfold parafSummand
  rw [if_neg]
  rintro ⟨_, _, h⟩
  exact hne h














noncomputable def combinedSummand (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (v du : ℂ)
    (ts : List ℤ) : ℂ :=
  ((v + du) - v) * parafSummand region a h0 (v + du) (5/8) hexChi ts
    + ((v + hexOmega * du) - v)
        * parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi ts
    + ((v + hexOmega ^ 2 * du) - v)
        * parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts



theorem combinedSummand_at_p {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) {ts : List ℤ} (hend : (ofTurns a h0 ts).EndsAt (v + du)) :
    combinedSummand region a h0 v du ts
      = ((v + du) - v) * parafSummand region a h0 (v + du) (5/8) hexChi ts := by
  unfold combinedSummand
  rw [parafSummand_eq_zero_of_not_endsAt region a h0 (v + hexOmega * du) _ _ ts
        (fun hq => hexMid_p_ne_q hdu (hend.symm.trans hq)),
      parafSummand_eq_zero_of_not_endsAt region a h0 (v + hexOmega ^ 2 * du) _ _ ts
        (fun hr => hexMid_p_ne_r hdu (hend.symm.trans hr))]
  ring



theorem combinedSummand_at_q {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) {ts : List ℤ} (hend : (ofTurns a h0 ts).EndsAt (v + hexOmega * du)) :
    combinedSummand region a h0 v du ts
      = ((v + hexOmega * du) - v)
          * parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi ts := by
  unfold combinedSummand
  rw [parafSummand_eq_zero_of_not_endsAt region a h0 (v + du) _ _ ts
        (fun hp => hexMid_p_ne_q hdu (hp.symm.trans hend)),
      parafSummand_eq_zero_of_not_endsAt region a h0 (v + hexOmega ^ 2 * du) _ _ ts
        (fun hr => hexMid_q_ne_r hdu (hend.symm.trans hr))]
  ring



theorem combinedSummand_at_r {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) {ts : List ℤ} (hend : (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du)) :
    combinedSummand region a h0 v du ts
      = ((v + hexOmega ^ 2 * du) - v)
          * parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts := by
  unfold combinedSummand
  rw [parafSummand_eq_zero_of_not_endsAt region a h0 (v + du) _ _ ts
        (fun hp => hexMid_p_ne_r hdu (hp.symm.trans hend)),
      parafSummand_eq_zero_of_not_endsAt region a h0 (v + hexOmega * du) _ _ ts
        (fun hq => hexMid_q_ne_r hdu (hq.symm.trans hend))]
  ring





theorem vertexSum_eq_tsum_combinedSummand (region : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (v du : ℂ)
    (hp : Summable fun ts => parafSummand region a h0 (v + du) (5/8) hexChi ts)
    (hq : Summable fun ts => parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi ts)
    (hr : Summable fun ts => parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts) :
    ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi
      = ∑' ts, combinedSummand region a h0 v du ts := by
  unfold parafObservable combinedSummand
  rw [← hp.tsum_mul_left, ← hq.tsum_mul_left, ← hr.tsum_mul_left]
  rw [← (hp.mul_left _).tsum_add (hq.mul_left _), ← ((hp.mul_left _).add (hq.mul_left _)).tsum_add (hr.mul_left _)]









































structure HexVertexEnumeration (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (v du : ℂ) where
  
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

namespace HexVertexEnumeration

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
















theorem relation (E : HexVertexEnumeration region a h0 v du) :
    ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 := by
  rw [E.reindex]
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · intro T hT
    exact genuine_triplet_zero region a h0 v du (E.tripBase T)
      (E.tripP_valid T hT) (E.tripQ_valid T hT) (E.tripR_valid T hT)
  · intro P hP
    exact genuine_pair_zero region a h0 v du (E.pairBase P) (E.pairLq P) (E.pairLr P)
      (E.pairLq_sum P hP) (E.pairLr_sum P hP) (E.pairLen P hP)
      (E.pairQ_valid P hP) (E.pairR_valid P hP)













noncomputable def toVertexWalkData (E : HexVertexEnumeration region a h0 v du) :
    VertexWalkData where
  du := du
  pairs := E.pairs
  pairWind := fun P => (ofTurns a h0 (E.pairBase P)).turnCount
  pairLen := fun P => (ofTurns a h0 (E.pairBase P ++ E.pairLq P)).numVertices
  triplets := E.triplets
  tripWind := fun T => (ofTurns a h0 (E.tripBase T)).turnCount
  tripLen := fun T => (ofTurns a h0 (E.tripBase T)).numVertices




theorem vertexSum_toVertexWalkData (E : HexVertexEnumeration region a h0 v du) :
    ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi
      = (toVertexWalkData E).vertexSum := by
  rw [E.reindex]
  unfold toVertexWalkData VertexWalkData.vertexSum
  simp only
  congr 1
  · 
    apply Finset.sum_congr rfl
    intro P hP
    rw [hexContribution_eq_paraf region a h0 (v + hexOmega * du) v (E.pairBase P ++ E.pairLq P)
          (E.pairQ_valid P hP),
        hexContribution_eq_paraf region a h0 (v + hexOmega ^ 2 * du) v (E.pairBase P ++ E.pairLr P)
          (E.pairR_valid P hP)]
    rw [turnCount_append_block a h0 (E.pairBase P) (E.pairLq P),
        turnCount_append_block a h0 (E.pairBase P) (E.pairLr P),
        E.pairLq_sum P hP, E.pairLr_sum P hP]
    have hnr : (ofTurns a h0 (E.pairBase P ++ E.pairLr P)).numVertices
        = (ofTurns a h0 (E.pairBase P ++ E.pairLq P)).numVertices := by
      simp only [numVertices, ofTurns, List.length_append]
      rw [E.pairLen P hP]
    rw [hnr]
    have e2 : ((ofTurns a h0 (E.pairBase P)).turnCount + (-4 : ℤ))
        = (ofTurns a h0 (E.pairBase P)).turnCount - 4 := by ring
    rw [e2]
    simp only [add_sub_cancel_left]
  · 
    apply Finset.sum_congr rfl
    intro T hT
    rw [hexContribution_eq_paraf region a h0 (v + du) v (E.tripBase T) (E.tripP_valid T hT),
        hexContribution_eq_paraf region a h0 (v + hexOmega * du) v (E.tripBase T ++ [-1])
          (E.tripQ_valid T hT),
        hexContribution_eq_paraf region a h0 (v + hexOmega ^ 2 * du) v (E.tripBase T ++ [1])
          (E.tripR_valid T hT)]
    rw [turnCount_concat a h0 (-1) (E.tripBase T), turnCount_concat a h0 1 (E.tripBase T),
        numVertices_concat a h0 (-1) (E.tripBase T), numVertices_concat a h0 1 (E.tripBase T)]
    have e1 : ((ofTurns a h0 (E.tripBase T)).turnCount + (-1 : ℤ))
        = (ofTurns a h0 (E.tripBase T)).turnCount - 1 := by ring
    rw [e1]
    simp only [add_sub_cancel_left]






theorem relation_via_vertexWalkData (E : HexVertexEnumeration region a h0 v du) :
    ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 := by
  rw [vertexSum_toVertexWalkData E, VertexWalkData.relation]





















def slotTurns (E : HexVertexEnumeration region a h0 v du) :
    ((E.pairs × Bool) ⊕ (E.triplets × Fin 3)) → List ℤ
  | Sum.inl (P, false) => E.pairBase P ++ E.pairLq P
  | Sum.inl (P, true)  => E.pairBase P ++ E.pairLr P
  | Sum.inr (T, ⟨0, _⟩) => E.tripBase T
  | Sum.inr (T, ⟨1, _⟩) => E.tripBase T ++ [-1]
  | Sum.inr (T, _)      => E.tripBase T ++ [1]





theorem tsum_combinedSummand_slot_eq_zero (E : HexVertexEnumeration region a h0 v du)
    (hdu : du ≠ 0) :
    ∑' slot, combinedSummand region a h0 v du (slotTurns E slot) = 0 := by
  rw [tsum_fintype, Fintype.sum_sum_type]
  have h1 : ∑ x : E.pairs × Bool,
      combinedSummand region a h0 v du (slotTurns E (Sum.inl x)) = 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    rintro ⟨P, hP⟩ _
    rw [Fintype.sum_bool]
    
    show combinedSummand region a h0 v du (E.pairBase P ++ E.pairLr P)
        + combinedSummand region a h0 v du (E.pairBase P ++ E.pairLq P) = 0
    rw [combinedSummand_at_r (du := du) hdu (E.pairR_valid P hP).2.2,
        combinedSummand_at_q (du := du) hdu (E.pairQ_valid P hP).2.2]
    rw [add_comm]
    exact genuine_pair_zero region a h0 v du (E.pairBase P) (E.pairLq P) (E.pairLr P)
      (E.pairLq_sum P hP) (E.pairLr_sum P hP) (E.pairLen P hP)
      (E.pairQ_valid P hP) (E.pairR_valid P hP)
  have h2 : ∑ x : E.triplets × Fin 3,
      combinedSummand region a h0 v du (slotTurns E (Sum.inr x)) = 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    rintro ⟨T, hT⟩ _
    rw [Fin.sum_univ_three]
    show combinedSummand region a h0 v du (E.tripBase T)
        + combinedSummand region a h0 v du (E.tripBase T ++ [-1])
        + combinedSummand region a h0 v du (E.tripBase T ++ [1]) = 0
    rw [combinedSummand_at_p (du := du) hdu (E.tripP_valid T hT).2.2,
        combinedSummand_at_q (du := du) hdu (E.tripQ_valid T hT).2.2,
        combinedSummand_at_r (du := du) hdu (E.tripR_valid T hT).2.2]
    exact genuine_triplet_zero region a h0 v du (E.tripBase T)
      (E.tripP_valid T hT) (E.tripQ_valid T hT) (E.tripR_valid T hT)
  rw [h1, h2, add_zero]

















theorem relation_of_bijection (E : HexVertexEnumeration region a h0 v du)
    (hdu : du ≠ 0)
    (hp : Summable fun ts => parafSummand region a h0 (v + du) (5/8) hexChi ts)
    (hq : Summable fun ts => parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi ts)
    (hr : Summable fun ts => parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts)
    (hinj : Function.Injective
      fun x : Function.support (combinedSummand region a h0 v du ∘ slotTurns E) =>
        slotTurns E x.1)
    (hsub : Function.support (combinedSummand region a h0 v du) ⊆
      Set.range fun x : Function.support (combinedSummand region a h0 v du ∘ slotTurns E) =>
        slotTurns E x.1) :
    ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 := by
  rw [vertexSum_eq_tsum_combinedSummand region a h0 v du hp hq hr]
  
  rw [tsum_eq_tsum_of_ne_zero_bij
        (g := combinedSummand region a h0 v du ∘ slotTurns E)
        (fun x => slotTurns E x.1) hinj hsub (fun _ => rfl)]
  
  exact tsum_combinedSummand_slot_eq_zero E hdu

end HexVertexEnumeration








noncomputable def HexVertexEnumeration.empty (region : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (hzero : ∀ z, parafObservable region a h0 z (5/8) hexChi = 0) :
    HexVertexEnumeration region a h0 v du where
  pairs := ∅
  pairBase := fun _ => []
  pairLq := fun _ => []
  pairLr := fun _ => []
  pairLq_sum := by simp
  pairLr_sum := by simp
  pairLen := by simp
  pairQ_valid := by simp
  pairR_valid := by simp
  triplets := ∅
  tripBase := fun _ => []
  tripP_valid := by simp
  tripQ_valid := by simp
  tripR_valid := by simp
  reindex := by simp [hzero]

end StatMech.Universality

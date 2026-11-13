/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.Universality.HexEndpointLocalGeometry

namespace StatMech.Universality

open HexWalk

noncomputable section

private theorem hexEndpoint_succ_ne_self (j : Fin 3) :
    hexCyclicSucc j ≠ j := by
  fin_cases j <;> decide

private theorem hexEndpoint_pred_ne_self (j : Fin 3) :
    hexCyclicPred j ≠ j := by
  fin_cases j <;> decide



theorem specialMidCount_append_one_of_base_one
    {a : ℂ} {h0 : ℤ} {v du : ℂ} (hdu : du ≠ 0)
    {base : List ℤ} {t : ℤ} {j l : Fin 3}
    (hjl : j ≠ l)
    (hbaseEnd : (ofTurns a h0 base).EndsAt (labelMid v du j))
    (hextEnd : (ofTurns a h0 (base ++ [t])).EndsAt (labelMid v du l))
    (hbaseCount : specialMidCount a h0 v du base = 1) :
    specialMidCount a h0 v du (base ++ [t]) = 2 := by
  classical
  have hnew : hexCyclicNewMid a h0 base t = labelMid v du l := by
    unfold HexWalk.EndsAt at hextEnd
    rw [hexInfra_endMid_eq_midAccum,
      hexCyclic_midAccum_append_single] at hextEnd
    exact hextEnd
  have hmids : (ofTurns a h0 (base ++ [t])).mids =
      (ofTurns a h0 base).mids ++ [labelMid v du l] := by
    change midsAux a h0 (base ++ [t]) =
      midsAux a h0 base ++ [labelMid v du l]
    rw [hexCyclic_midsAux_append_single]
    simpa [hexCyclicNewMid] using hnew
  have hjpass : PassesThrough a h0 base (labelMid v du j) :=
    hexClass_endsAt_passesThrough base (labelMid v du j) hbaseEnd
  have hpq := hexMid_p_ne_q (v := v) hdu
  have hpr := hexMid_p_ne_r (v := v) hdu
  have hqr := hexMid_q_ne_r (v := v) hdu
  have hrq : hexOmega ^ 2 ≠ hexOmega := Ne.symm hexOmega_ne_sq
  fin_cases j <;> fin_cases l
  all_goals
    simp only [specialMidCount, PassesThrough] at hbaseCount hjpass ⊢
    simp only [hmids, List.mem_append, List.mem_singleton] at *
    simp only [labelMid] at *
    by_cases hp : v + du ∈ (ofTurns a h0 base).mids
    all_goals by_cases hq :
      v + hexOmega * du ∈ (ofTurns a h0 base).mids
    all_goals by_cases hr :
      v + hexOmega ^ 2 * du ∈ (ofTurns a h0 base).mids
    all_goals simp_all



theorem HexEndpointCyclicTriplet.extension_counts_of_base_one
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (C : HexEndpointCyclicTriplet region a h0 v du)
    (hdu : du ≠ 0)
    (hbaseCount : specialMidCount a h0 v du C.base = 1) :
    specialMidCount a h0 v du (C.base ++ [-1]) = 2 ∧
      specialMidCount a h0 v du (C.base ++ [1]) = 2 := by
  constructor
  · exact specialMidCount_append_one_of_base_one hdu
      (hexEndpoint_succ_ne_self C.baseLabel).symm
      C.base_valid.2.2 C.succ_valid.2.2 hbaseCount
  · exact specialMidCount_append_one_of_base_one hdu
      (hexEndpoint_pred_ne_self C.baseLabel).symm
      C.base_valid.2.2 C.pred_valid.2.2 hbaseCount


theorem HexEndpointCyclicTriplet.count_eq_one_or_two_of_mem
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (C : HexEndpointCyclicTriplet region a h0 v du)
    (hdu : du ≠ 0)
    (hbaseCount : specialMidCount a h0 v du C.base = 1)
    {ts : List ℤ} (hts : ts ∈ C.piece) :
    specialMidCount a h0 v du ts = 1 ∨
      specialMidCount a h0 v du ts = 2 := by
  have hext := C.extension_counts_of_base_one hdu hbaseCount
  simp only [HexEndpointCyclicTriplet.piece, Finset.mem_insert,
    Finset.mem_singleton] at hts
  rcases hts with hts | hts | hts
  · left
    simpa [hts] using hbaseCount
  · right
    simpa [hts] using hext.1
  · right
    simpa [hts] using hext.2



theorem HexEndpointCyclicTriplet.piece_eq_of_mem
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (C D : HexEndpointCyclicTriplet region a h0 v du)
    (hdu : du ≠ 0)
    (hCbase : specialMidCount a h0 v du C.base = 1)
    (hDbase : specialMidCount a h0 v du D.base = 1)
    {ts : List ℤ} (hC : ts ∈ C.piece) (hD : ts ∈ D.piece) :
    C.piece = D.piece := by
  have hCext := C.extension_counts_of_base_one hdu hCbase
  have hDext := D.extension_counts_of_base_one hdu hDbase
  simp only [HexEndpointCyclicTriplet.piece, Finset.mem_insert,
    Finset.mem_singleton] at hC hD
  have piece_eq_of_base_eq (hbase : C.base = D.base) : C.piece = D.piece := by
    simp [HexEndpointCyclicTriplet.piece, hbase]
  rcases hC with hC | hC | hC <;> rcases hD with hD | hD | hD
  · exact piece_eq_of_base_eq (hC.symm.trans hD)
  · exfalso
    have heq : C.base = D.base ++ [-1] := hC.symm.trans hD
    have htwo : specialMidCount a h0 v du C.base = 2 := by
      rw [heq]
      exact hDext.1
    have := hCbase.symm.trans htwo
    omega
  · exfalso
    have heq : C.base = D.base ++ [1] := hC.symm.trans hD
    have htwo : specialMidCount a h0 v du C.base = 2 := by
      rw [heq]
      exact hDext.2
    have := hCbase.symm.trans htwo
    omega
  · exfalso
    have heq : C.base ++ [-1] = D.base := hC.symm.trans hD
    have hone : specialMidCount a h0 v du (C.base ++ [-1]) = 1 := by
      rw [heq]
      exact hDbase
    have := hCext.1.symm.trans hone
    omega
  · apply piece_eq_of_base_eq
    have := congrArg List.dropLast (hC.symm.trans hD)
    simpa using this
  · apply piece_eq_of_base_eq
    have := congrArg List.dropLast (hC.symm.trans hD)
    simpa using this
  · exfalso
    have heq : C.base ++ [1] = D.base := hC.symm.trans hD
    have hone : specialMidCount a h0 v du (C.base ++ [1]) = 1 := by
      rw [heq]
      exact hDbase
    have := hCext.2.symm.trans hone
    omega
  · apply piece_eq_of_base_eq
    have := congrArg List.dropLast (hC.symm.trans hD)
    simpa using this
  · apply piece_eq_of_base_eq
    have := congrArg List.dropLast (hC.symm.trans hD)
    simpa using this



theorem HexEndpointCyclicTriplet.disjoint_cyclicLoopPair_of_counts
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (C : HexEndpointCyclicTriplet region a h0 v du)
    (P : HexEndpointCyclicLoopPair region a h0 v du)
    (hdu : du ≠ 0)
    (hCbase : specialMidCount a h0 v du C.base = 1)
    (hPsucc : specialMidCount a h0 v du (P.base ++ P.loopQ) = 3)
    (hPpred : specialMidCount a h0 v du
      (P.base ++ hexEndpointLoopPartner P.loopQ) = 3) :
    Disjoint C.piece P.piece := by
  rw [Finset.disjoint_left]
  intro ts hC hP
  have hCcount := C.count_eq_one_or_two_of_mem hdu hCbase hC
  simp only [HexEndpointCyclicLoopPair.piece, Finset.mem_insert,
    Finset.mem_singleton] at hP
  rcases hP with hP | hP
  · rcases hCcount with hCcount | hCcount
    · have := hCcount.symm.trans (hP ▸ hPsucc)
      omega
    · have := hCcount.symm.trans (hP ▸ hPsucc)
      omega
  · rcases hCcount with hCcount | hCcount
    · have := hCcount.symm.trans (hP ▸ hPpred)
      omega
    · have := hCcount.symm.trans (hP ▸ hPpred)
      omega




theorem HexEndpointCyclicLoopPair.piece_eq_of_mem_of_shared_stem
    {region : ℂ → Prop} {v du : ℂ}
    (P Q : HexEndpointCyclicLoopPair region hexAWStart 1 v du)
    (hPstem : hexInfra_midAccum hexAWStart 1 P.base +
      halfStep (hexInfra_headAccum 1 P.base) = v)
    (hQstem : hexInfra_midAccum hexAWStart 1 Q.base +
      halfStep (hexInfra_headAccum 1 Q.base) = v)
    {ts : List ℤ} (hPmem : ts ∈ P.piece) (hQmem : ts ∈ Q.piece) :
    P.piece = Q.piece := by
  have hPcases := hPmem
  have hQcases := hQmem
  simp only [HexEndpointCyclicLoopPair.piece, Finset.mem_insert,
    Finset.mem_singleton] at hPcases hQcases
  have hsaw : (ofTurns hexAWStart 1 ts).EndpointIsSAW := by
    rcases hPcases with hP | hP
    · rw [hP]
      exact P.succ_valid.1.2
    · rw [hP]
      exact P.pred_valid.1.2
  have hPprefix : ts.take P.base.length = P.base := by
    rcases hPcases with hP | hP <;> rw [hP] <;> simp
  have hQprefix : ts.take Q.base.length = Q.base := by
    rcases hQcases with hQ | hQ <;> rw [hQ] <;> simp
  have hPlt : P.base.length < ts.length := by
    obtain ⟨tail, hloop⟩ := P.loopQ_first
    rcases hPcases with hP | hP
    · rw [hP, hloop]
      simp
    · rw [hP, hloop]
      simp [hexEndpointLoopPartner]
  have hQlt : Q.base.length < ts.length := by
    obtain ⟨tail, hloop⟩ := Q.loopQ_first
    rcases hQcases with hQ | hQ
    · rw [hQ, hloop]
      simp
    · rw [hQ, hloop]
      simp [hexEndpointLoopPartner]
  have hPpos : hexJordan_vertexPos hexAWStart 1 ts P.base.length = v := by
    unfold hexJordan_vertexPos
    rw [hPprefix]
    exact hPstem
  have hQpos : hexJordan_vertexPos hexAWStart 1 ts Q.base.length = v := by
    unfold hexJordan_vertexPos
    rw [hQprefix]
    exact hQstem
  have hlen : P.base.length = Q.base.length := by
    by_contra hne
    exact (hexEndpoint_vertexPos_ne_of_saw ts hsaw
      P.base.length Q.base.length hPlt hQlt hne)
        (hPpos.trans hQpos.symm)
  have hbase : P.base = Q.base := by
    rw [← hPprefix, ← hQprefix, hlen]
  rcases hPcases with hP | hP <;> rcases hQcases with hQ | hQ
  · have hloop : P.loopQ = Q.loopQ := by
      simpa [hbase] using hP.symm.trans hQ
    simp [HexEndpointCyclicLoopPair.piece, hbase, hloop]
  · have hloop : P.loopQ = hexEndpointLoopPartner Q.loopQ := by
      simpa [hbase] using hP.symm.trans hQ
    ext x
    simp [HexEndpointCyclicLoopPair.piece, hbase, hloop, or_comm]
  · have hpartner : hexEndpointLoopPartner P.loopQ = Q.loopQ := by
      simpa [hbase] using hP.symm.trans hQ
    have hloop : P.loopQ = hexEndpointLoopPartner Q.loopQ := by
      calc
        P.loopQ = hexEndpointLoopPartner
            (hexEndpointLoopPartner P.loopQ) :=
          (hexEndpointLoopPartner_involutive P.loopQ).symm
        _ = hexEndpointLoopPartner Q.loopQ :=
          congrArg hexEndpointLoopPartner hpartner
    ext x
    simp [HexEndpointCyclicLoopPair.piece, hbase, hloop, or_comm]
  · have hpartner : hexEndpointLoopPartner P.loopQ =
        hexEndpointLoopPartner Q.loopQ := by
      simpa [hbase] using hP.symm.trans hQ
    have hloop : P.loopQ = Q.loopQ := by
      have := congrArg hexEndpointLoopPartner hpartner
      simpa using this
    simp [HexEndpointCyclicLoopPair.piece, hbase, hloop]

end

end StatMech.Universality

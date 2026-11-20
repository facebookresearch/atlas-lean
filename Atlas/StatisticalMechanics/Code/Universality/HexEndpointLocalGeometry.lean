/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Universality.HexEndpointVertex
import Code.Universality.HexBrickUmlaufsatz

namespace StatMech.Universality

open Complex Function HexWalk

noncomputable section



theorem hexEndpoint_vertexPos_ne_of_saw
    (ts : List ℤ) (hsaw : (ofTurns hexAWStart 1 ts).EndpointIsSAW)
    (i j : ℕ) (hi : i < ts.length) (hj : j < ts.length) (hne : i ≠ j) :
    hexJordan_vertexPos hexAWStart 1 ts i ≠
      hexJordan_vertexPos hexAWStart 1 ts j := by
  intro heq
  have hilen : i < (verticesAux hexAWStart 1 ts).length := by
    rw [length_verticesAux]
    omega
  have hjlen : j < (verticesAux hexAWStart 1 ts).length := by
    rw [length_verticesAux]
    omega
  have hidrop : i < (verticesAux hexAWStart 1 ts).dropLast.length := by
    rw [List.length_dropLast, length_verticesAux]
    omega
  have hjdrop : j < (verticesAux hexAWStart 1 ts).dropLast.length := by
    rw [List.length_dropLast, length_verticesAux]
    omega
  have hvi := hexJordan_verticesAux_getElem?_eq
    hexAWStart 1 ts i (le_of_lt hi)
  have hvj := hexJordan_verticesAux_getElem?_eq
    hexAWStart 1 ts j (le_of_lt hj)
  rw [List.getElem?_eq_getElem hilen, Option.some.injEq] at hvi
  rw [List.getElem?_eq_getElem hjlen, Option.some.injEq] at hvj
  have hget : (verticesAux hexAWStart 1 ts).dropLast[i] =
      (verticesAux hexAWStart 1 ts).dropLast[j] := by
    rw [List.getElem_dropLast hidrop, List.getElem_dropLast hjdrop,
      hvi, hvj]
    exact heq
  exact hne ((List.getElem_inj hsaw).mp hget)



theorem hexEndpoint_vertexPos_eq_nextMid_sub
    (ts : List ℤ) (k : ℕ) (hk : k < ts.length) :
    hexJordan_vertexPos hexAWStart 1 ts k =
      hexInfra_midAccum hexAWStart 1 (ts.take (k + 1)) -
        halfStep (hexInfra_headAccum 1 (ts.take (k + 1))) := by
  rw [List.take_succ_eq_append_getElem hk,
    hexCyclic_midAccum_append_single]
  unfold hexJordan_vertexPos
  simp only [hexInfra_headAccum_eq_add_sum, List.sum_append,
    List.sum_singleton]
  ring



theorem hexEndpoint_edge_endpoint_cases
    (ts : List ℤ) (c : HexAWCoord) (e : Fin 3)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hmid : hexInfra_midAccum hexAWStart 1 ts = hexAWMid c e) :
    (hexInfra_midAccum hexAWStart 1 ts +
          halfStep (hexInfra_headAccum 1 ts) = hexAWPos c ∧
        hexInfra_midAccum hexAWStart 1 ts -
          halfStep (hexInfra_headAccum 1 ts) =
            hexAWPos (hexAWNeighbor c e)) ∨
      (hexInfra_midAccum hexAWStart 1 ts +
          halfStep (hexInfra_headAccum 1 ts) =
            hexAWPos (hexAWNeighbor c e) ∧
        hexInfra_midAccum hexAWStart 1 ts -
          halfStep (hexInfra_headAccum 1 ts) = hexAWPos c) := by
  rcases hexEndpoint_forward_vertex_of_mid ts c e hlegal hmid with
      hforward | hforward
  · left
    refine ⟨hforward, ?_⟩
    unfold hexAWMid at hmid
    linear_combination 2 * hmid - hforward
  · right
    refine ⟨hforward, ?_⟩
    unfold hexAWMid at hmid
    linear_combination 2 * hmid - hforward





theorem hexEndpoint_final_mid_fresh_aw
    (base : List ℤ) (t : ℤ) (c : HexAWCoord) (e : Fin 3)
    (hlegal : (ofTurns hexAWStart 1 (base ++ [t])).EndpointIsLegalSAW)
    (hend : (ofTurns hexAWStart 1 (base ++ [t])).EndsAt (hexAWMid c e))
    (hne : hexAWMid c e ≠ hexAWStart) :
    ¬PassesThrough hexAWStart 1 base (hexAWMid c e) := by
  intro hpass
  unfold PassesThrough HexWalk.mids at hpass
  change hexAWMid c e ∈ midsAux hexAWStart 1 base at hpass
  rw [List.mem_iff_getElem] at hpass
  obtain ⟨k, hklist, hkget⟩ := hpass
  have hk : k ≤ base.length := by
    rw [length_midsAux] at hklist
    omega
  have hget := hexJordan_midsAux_getElem?_eq hexAWStart 1 base k hk
  rw [List.getElem?_eq_getElem hklist, Option.some.injEq] at hget
  have hmid : hexInfra_midAccum hexAWStart 1 (base.take k) =
      hexAWMid c e := hget.symm.trans hkget
  have hkpos : 0 < k := by
    by_contra hkzero
    have : k = 0 := by omega
    subst k
    simp only [List.take_zero, hexInfra_midAccum_nil] at hmid
    exact hne hmid.symm
  have ht : t = 1 ∨ t = -1 :=
    hlegal.1 t (by simp)
  have hfullMid : hexInfra_midAccum hexAWStart 1 (base ++ [t]) =
      hexAWMid c e := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact hend
  by_cases hklast : k = base.length
  · have hbaseMid : hexInfra_midAccum hexAWStart 1 base =
        hexAWMid c e := by
      simpa [hklast] using hmid
    have hnew := hexCyclic_midAccum_append_single hexAWStart 1 t base
    have hsame : hexInfra_midAccum hexAWStart 1 (base ++ [t]) =
        hexInfra_midAccum hexAWStart 1 base := hfullMid.trans hbaseMid.symm
    apply hexW1_halfStep_add_ne_zero (hexInfra_headAccum 1 base) t ht
    linear_combination -hnew + hsame
  · have hklt : k < base.length := by omega
    let full := base ++ [t]
    have hfullLegal : ∀ u ∈ full, u = 1 ∨ u = -1 := hlegal.1
    have htakeLegal : ∀ u ∈ full.take k, u = 1 ∨ u = -1 := by
      intro u hu
      exact hfullLegal u (List.mem_of_mem_take hu)
    have htakeMid : hexInfra_midAccum hexAWStart 1 (full.take k) =
        hexAWMid c e := by
      simpa [full, List.take_append_of_le_length hk] using hmid
    have hearly := hexEndpoint_edge_endpoint_cases
      (full.take k) c e htakeLegal htakeMid
    have hfinal := hexEndpoint_edge_endpoint_cases
      full c e hfullLegal (by simpa [full] using hfullMid)
    have hfinalPos : hexJordan_vertexPos hexAWStart 1 full base.length =
        hexInfra_midAccum hexAWStart 1 full -
          halfStep (hexInfra_headAccum 1 full) := by
      have h := hexEndpoint_vertexPos_eq_nextMid_sub
        full base.length (by simp [full])
      have htake : full.take (base.length + 1) = full := by
        rw [show base.length + 1 = full.length by simp [full], List.take_length]
      rw [htake] at h
      exact h
    have hcurPos : hexJordan_vertexPos hexAWStart 1 full k =
        hexInfra_midAccum hexAWStart 1 (full.take k) +
          halfStep (hexInfra_headAccum 1 (full.take k)) := rfl
    have hpredPos : hexJordan_vertexPos hexAWStart 1 full (k - 1) =
        hexInfra_midAccum hexAWStart 1 (full.take k) -
          halfStep (hexInfra_headAccum 1 (full.take k)) := by
      have h := hexEndpoint_vertexPos_eq_nextMid_sub full (k - 1) (by
        simp [full]
        omega)
      have hkback : k - 1 + 1 = k := by omega
      rw [hkback] at h
      exact h
    have hfinalLt : base.length < full.length := by simp [full]
    have hcurLt : k < full.length := by simp [full]; omega
    have hpredLt : k - 1 < full.length := by simp [full]; omega
    rcases hearly with hearly | hearly <;>
      rcases hfinal with hfinal | hfinal
    · apply (hexEndpoint_vertexPos_ne_of_saw full hlegal.2
        base.length (k - 1) hfinalLt hpredLt (by omega))
      rw [hfinalPos, hpredPos, hfinal.2, hearly.2]
    · apply (hexEndpoint_vertexPos_ne_of_saw full hlegal.2
        base.length k hfinalLt hcurLt (by omega))
      rw [hfinalPos, hcurPos, hfinal.2, hearly.1]
    · apply (hexEndpoint_vertexPos_ne_of_saw full hlegal.2
        base.length k hfinalLt hcurLt (by omega))
      rw [hfinalPos, hcurPos, hfinal.2, hearly.1]
    · apply (hexEndpoint_vertexPos_ne_of_saw full hlegal.2
        base.length (k - 1) hfinalLt hpredLt (by omega))
      rw [hfinalPos, hpredPos, hfinal.2, hearly.2]



theorem hexAWMid_edge_injective (c : HexAWCoord) :
    Function.Injective (hexAWMid c) := by
  intro e f hef
  rcases (hexAWMid_eq_iff c c e f).mp hef with h | h
  · exact h.2.symm
  · exact h.2.symm



theorem hexEndpoint_count_two_other_base_mid
    (base : List ℤ) (t : ℤ) (c : HexAWCoord) (e : Fin 3)
    (hend : (ofTurns hexAWStart 1 (base ++ [t])).EndsAt (hexAWMid c e))
    (hnew : ¬PassesThrough hexAWStart 1 base (hexAWMid c e))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) (base ++ [t]) = 2) :
    ∃ f : Fin 3, f ≠ e ∧
      PassesThrough hexAWStart 1 base (hexAWMid c f) := by
  have hendMid : hexInfra_midAccum hexAWStart 1 (base ++ [t]) =
      hexAWMid c e := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact hend
  have hmids : (ofTurns hexAWStart 1 (base ++ [t])).mids =
      (ofTurns hexAWStart 1 base).mids ++ [hexAWMid c e] := by
    change midsAux hexAWStart 1 (base ++ [t]) =
      midsAux hexAWStart 1 base ++ [hexAWMid c e]
    rw [hexCyclic_midsAux_append_single]
    rw [hexCyclic_midAccum_append_single] at hendMid
    rw [hendMid]
  have hpassFull (f : Fin 3) :
      PassesThrough hexAWStart 1 (base ++ [t]) (hexAWMid c f) ↔
        PassesThrough hexAWStart 1 base (hexAWMid c f) ∨ f = e := by
    unfold PassesThrough
    rw [hmids, List.mem_append, List.mem_singleton]
    exact or_congr_right (hexAWMid_edge_injective c |>.eq_iff)
  have hlabel0 : hexAWPos c + (hexAWMid c 0 - hexAWPos c) =
      hexAWMid c 0 := by ring
  have hlabel1 : hexAWPos c +
      hexOmega * (hexAWMid c 0 - hexAWPos c) = hexAWMid c 1 := by
    simpa [labelMid] using hexAW_labelMid_eq_mid c 1
  have hlabel2 : hexAWPos c +
      hexOmega ^ 2 * (hexAWMid c 0 - hexAWPos c) = hexAWMid c 2 := by
    simpa [labelMid] using hexAW_labelMid_eq_mid c 2
  simp only [specialMidCount] at hcount
  rw [hlabel0, hlabel1, hlabel2, hpassFull 0, hpassFull 1,
    hpassFull 2] at hcount
  fin_cases e
  · by_cases h1 : PassesThrough hexAWStart 1 base (hexAWMid c 1)
    · exact ⟨1, by decide, h1⟩
    · have h2 : PassesThrough hexAWStart 1 base (hexAWMid c 2) := by
        by_contra hn2
        simp_all
      exact ⟨2, by decide, h2⟩
  · by_cases h0 : PassesThrough hexAWStart 1 base (hexAWMid c 0)
    · exact ⟨0, by decide, h0⟩
    · have h2 : PassesThrough hexAWStart 1 base (hexAWMid c 2) := by
        by_contra hn2
        simp_all
      exact ⟨2, by decide, h2⟩
  · by_cases h0 : PassesThrough hexAWStart 1 base (hexAWMid c 0)
    · exact ⟨0, by decide, h0⟩
    · have h1 : PassesThrough hexAWStart 1 base (hexAWMid c 1) := by
        by_contra hn1
        simp_all
      exact ⟨1, by decide, h1⟩



theorem hexAW_specialMidCount_three_of_all
    (ts : List ℤ) (c : HexAWCoord)
    (hall : ∀ e : Fin 3,
      PassesThrough hexAWStart 1 ts (hexAWMid c e)) :
    specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3 := by
  have hlabel0 : hexAWPos c + (hexAWMid c 0 - hexAWPos c) =
      hexAWMid c 0 := by ring
  have hlabel1 : hexAWPos c +
      hexOmega * (hexAWMid c 0 - hexAWPos c) = hexAWMid c 1 := by
    simpa [labelMid] using hexAW_labelMid_eq_mid c 1
  have hlabel2 : hexAWPos c +
      hexOmega ^ 2 * (hexAWMid c 0 - hexAWPos c) = hexAWMid c 2 := by
    simpa [labelMid] using hexAW_labelMid_eq_mid c 2
  unfold specialMidCount
  rw [hlabel0, hlabel1, hlabel2]
  simp [hall]



theorem hexAW_all_mids_of_specialMidCount_three
    (ts : List ℤ) (c : HexAWCoord)
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3) :
    ∀ e : Fin 3, PassesThrough hexAWStart 1 ts (hexAWMid c e) := by
  have hlabel0 : hexAWPos c + (hexAWMid c 0 - hexAWPos c) =
      hexAWMid c 0 := by ring
  have hlabel1 : hexAWPos c +
      hexOmega * (hexAWMid c 0 - hexAWPos c) = hexAWMid c 1 := by
    simpa [labelMid] using hexAW_labelMid_eq_mid c 1
  have hlabel2 : hexAWPos c +
      hexOmega ^ 2 * (hexAWMid c 0 - hexAWPos c) = hexAWMid c 2 := by
    simpa [labelMid] using hexAW_labelMid_eq_mid c 2
  simp only [specialMidCount, hlabel0, hlabel1, hlabel2] at hcount
  intro e
  fin_cases e <;>
    by_cases h0 : PassesThrough hexAWStart 1 ts (hexAWMid c 0) <;>
    by_cases h1 : PassesThrough hexAWStart 1 ts (hexAWMid c 1) <;>
    by_cases h2 : PassesThrough hexAWStart 1 ts (hexAWMid c 2) <;>
    simp_all



theorem hexEndpoint_passes_iff_prefix
    (ts : List ℤ) (z : ℂ) :
    PassesThrough hexAWStart 1 ts z ↔
      ∃ k, k ≤ ts.length ∧
        hexInfra_midAccum hexAWStart 1 (ts.take k) = z := by
  constructor
  · intro hz
    unfold PassesThrough HexWalk.mids at hz
    change z ∈ midsAux hexAWStart 1 ts at hz
    rw [List.mem_iff_getElem] at hz
    obtain ⟨k, hklen, hk⟩ := hz
    have hkle : k ≤ ts.length := by
      rw [length_midsAux] at hklen
      omega
    have hget := hexJordan_midsAux_getElem?_eq
      hexAWStart 1 ts k hkle
    rw [List.getElem?_eq_getElem hklen, Option.some.injEq] at hget
    exact ⟨k, hkle, hget.symm.trans hk⟩
  · rintro ⟨k, hk, rfl⟩
    exact hexEndpoint_prefix_mid_mem hexAWStart 1 ts k hk


structure HexEndpointLocalCrossing (ts : List ℤ) (c : HexAWCoord) where
  index : ℕ
  index_lt : index < ts.length
  before : Fin 3
  after : Fin 3
  before_ne_after : before ≠ after
  before_mid : hexInfra_midAccum hexAWStart 1 (ts.take index) =
    hexAWMid c before
  at_vertex : hexInfra_midAccum hexAWStart 1 (ts.take index) +
    halfStep (hexInfra_headAccum 1 (ts.take index)) = hexAWPos c
  after_mid : hexInfra_midAccum hexAWStart 1 (ts.take (index + 1)) =
    hexAWMid c after



theorem hexEndpoint_local_crossing_of_internal_mid
    (ts : List ℤ) (c : HexAWCoord) (e : Fin 3) (k : ℕ)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (hk : k < ts.length)
    (hmid : hexInfra_midAccum hexAWStart 1 (ts.take k) =
      hexAWMid c e) :
    Nonempty (HexEndpointLocalCrossing ts c) := by
  have htakeLegal : ∀ u ∈ ts.take k, u = 1 ∨ u = -1 := by
    intro u hu
    exact hlegal.1 u (List.mem_of_mem_take hu)
  rcases hexEndpoint_forward_vertex_of_mid (ts.take k) c e
      htakeLegal hmid with hforward | hforward
  · let t := ts[k]
    have ht : t = 1 ∨ t = -1 := hlegal.1 t (List.getElem_mem hk)
    obtain ⟨f, hfe, hnext⟩ :=
      hexEndpoint_next_mid_of_forward_vertex
        (ts.take k) t c e htakeLegal ht hmid hforward
    refine ⟨⟨k, hk, e, f, hfe.symm, hmid, hforward, ?_⟩⟩
    rw [List.take_succ_eq_append_getElem hk]
    simpa only [t] using hnext
  · have hkpos : 0 < k := by
      by_contra hk0
      have hkzero : k = 0 := by omega
      subst k
      simp only [List.take_zero, hexInfra_midAccum_nil] at hmid
      have hedge : hexAWMid hexAWOriginCoord 0 = hexAWMid c e :=
        hexAWMid_origin_zero.trans hmid
      rcases (hexAWMid_eq_iff hexAWOriginCoord c 0 e).mp hedge with
          ⟨hc, he⟩ | ⟨hc, he⟩
      · subst c
        subst e
        have hstartForward : hexAWStart + halfStep 1 =
            hexAWPos hexAWOriginCoord := by
          simp [hexAWStart, halfStep, hexAWOriginCoord, hexAWPos,
            show hexUnit 4 = -hexUnit 1 by
              simpa using hexUnit_add_three 1]
        have hpos : hexAWPos hexAWOriginCoord =
            hexAWPos (hexAWNeighbor hexAWOriginCoord 0) :=
          hstartForward.symm.trans hforward
        exact hexAWNeighbor_ne hexAWOriginCoord 0
          (hexAWPos_injective hpos).symm
      · exact hnotOutside hc
    let p := k - 1
    have hp : p < ts.length := by dsimp [p]; omega
    have hpk : p + 1 = k := by dsimp [p]; omega
    let t := ts[p]
    have ht : t = 1 ∨ t = -1 := hlegal.1 t (List.getElem_mem hp)
    have hpLegal : ∀ u ∈ ts.take p, u = 1 ∨ u = -1 := by
      intro u hu
      exact hlegal.1 u (List.mem_of_mem_take hu)
    have htakeK : ts.take k = ts.take p ++ [t] := by
      rw [← List.take_succ_eq_append_getElem hp, hpk]
    obtain ⟨f, hfe, hprev⟩ :=
      hexEndpoint_previous_mid_of_forward_outer
        (ts.take p) t c e hpLegal ht
          (by simpa only [htakeK] using hmid)
          (by simpa only [htakeK] using hforward)
    have hvertex : hexInfra_midAccum hexAWStart 1 (ts.take p) +
        halfStep (hexInfra_headAccum 1 (ts.take p)) = hexAWPos c := by
      have hstep := hexCyclic_midAccum_append_single
        hexAWStart 1 t (ts.take p)
      have hback : hexInfra_midAccum hexAWStart 1 (ts.take k) -
          halfStep (hexInfra_headAccum 1 (ts.take k)) = hexAWPos c := by
        have hedge := hexEndpoint_edge_endpoint_cases
          (ts.take k) c e htakeLegal hmid
        rcases hedge with hedge | hedge
        · have hpos : hexAWPos (hexAWNeighbor c e) = hexAWPos c :=
            hforward.symm.trans hedge.1
          exact (hexAWNeighbor_ne c e (hexAWPos_injective hpos)).elim
        · exact hedge.2
      have hhead : hexInfra_headAccum 1 (ts.take p ++ [t]) =
          hexInfra_headAccum 1 (ts.take p) + t := by
        simp [hexInfra_headAccum_eq_add_sum, List.sum_append]
        ring
      rw [htakeK] at hback
      rw [hhead] at hback
      linear_combination -hstep + hback
    refine ⟨⟨p, hp, f, e, hfe, hprev, hvertex, ?_⟩⟩
    rw [hpk]
    exact hmid




theorem hexEndpoint_local_crossing_of_count_three
    (ts : List ℤ) (c : HexAWCoord) (endEdge : Fin 3)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3) :
    Nonempty (HexEndpointLocalCrossing ts c) := by
  let other := hexCyclicSucc endEdge
  have hother : other ≠ endEdge := by
    dsimp [other]
    fin_cases endEdge <;> decide
  have hpass := hexAW_all_mids_of_specialMidCount_three ts c hcount other
  obtain ⟨k, hk, hmid⟩ :=
    (hexEndpoint_passes_iff_prefix ts (hexAWMid c other)).mp hpass
  have hklt : k < ts.length := by
    by_contra hnlt
    have hkeq : k = ts.length := by omega
    have hfinal : hexInfra_midAccum hexAWStart 1 (ts.take k) =
        hexAWMid c endEdge := by
      rw [hkeq, List.take_length]
      rw [← hexInfra_endMid_eq_midAccum]
      exact hend
    exact hother (hexAWMid_edge_injective c (hmid.symm.trans hfinal))
  exact hexEndpoint_local_crossing_of_internal_mid
    ts c other k hnotOutside hlegal hklt hmid



theorem HexEndpointLocalCrossing.internal_index_cases
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (e : Fin 3) (k : ℕ) (hk : k < ts.length)
    (hmid : hexInfra_midAccum hexAWStart 1 (ts.take k) =
      hexAWMid c e) :
    k = C.index ∨ k = C.index + 1 := by
  have htakeLegal : ∀ u ∈ ts.take k, u = 1 ∨ u = -1 := by
    intro u hu
    exact hlegal.1 u (List.mem_of_mem_take hu)
  rcases hexEndpoint_edge_endpoint_cases
      (ts.take k) c e htakeLegal hmid with hedge | hedge
  · left
    by_contra hne
    apply hexEndpoint_vertexPos_ne_of_saw ts hlegal.2
      k C.index hk C.index_lt hne
    unfold hexJordan_vertexPos
    exact hedge.1.trans C.at_vertex.symm
  · have hkpos : 0 < k := by
      by_contra hk0
      have hkzero : k = 0 := by omega
      subst k
      simp only [List.take_zero, hexInfra_midAccum_nil] at hmid
      have hsame : hexAWMid hexAWOriginCoord 0 = hexAWMid c e :=
        hexAWMid_origin_zero.trans hmid
      rcases (hexAWMid_eq_iff hexAWOriginCoord c 0 e).mp hsame with
          ⟨hc, he⟩ | ⟨hc, he⟩
      · subst c
        subst e
        have hstartForward : hexAWStart + halfStep 1 =
            hexAWPos hexAWOriginCoord := by
          simp [hexAWStart, halfStep, hexAWOriginCoord, hexAWPos,
            show hexUnit 4 = -hexUnit 1 by
              simpa using hexUnit_add_three 1]
        have hpos : hexAWPos hexAWOriginCoord =
            hexAWPos (hexAWNeighbor hexAWOriginCoord 0) :=
          hstartForward.symm.trans hedge.1
        exact hexAWNeighbor_ne hexAWOriginCoord 0
          (hexAWPos_injective hpos).symm
      · exact hnotOutside hc
    right
    have hkm1 : k - 1 < ts.length := by omega
    have hvertex : hexJordan_vertexPos hexAWStart 1 ts (k - 1) =
        hexAWPos c := by
      have hv := hexEndpoint_vertexPos_eq_nextMid_sub ts (k - 1) (by omega)
      have hsucc : k - 1 + 1 = k := by omega
      rw [hsucc] at hv
      exact hv.trans hedge.2
    have heq : k - 1 = C.index := by
      by_contra hne
      exact (hexEndpoint_vertexPos_ne_of_saw ts hlegal.2
        (k - 1) C.index hkm1 C.index_lt hne)
          (hvertex.trans C.at_vertex.symm)
    omega



theorem HexEndpointLocalCrossing.exists_third
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c) :
    ∃ e : Fin 3, e ≠ C.before ∧ e ≠ C.after := by
  rcases C with ⟨index, index_lt, before, after, hne,
    before_mid, at_vertex, after_mid⟩
  change ∃ e : Fin 3, e ≠ before ∧ e ≠ after
  fin_cases before <;> fin_cases after <;>
    simp_all <;>
    first | exact ⟨0, by decide, by decide⟩ |
      exact ⟨1, by decide, by decide⟩ |
      exact ⟨2, by decide, by decide⟩



theorem HexEndpointLocalCrossing.endEdge_ne
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (endEdge : Fin 3)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3) :
    endEdge ≠ C.before ∧ endEdge ≠ C.after := by
  obtain ⟨third, hthirdBefore, hthirdAfter⟩ := C.exists_third
  have hpass := hexAW_all_mids_of_specialMidCount_three ts c hcount third
  obtain ⟨k, hk, hmid⟩ :=
    (hexEndpoint_passes_iff_prefix ts (hexAWMid c third)).mp hpass
  have hkeq : k = ts.length := by
    by_contra hne
    have hklt : k < ts.length := by omega
    rcases C.internal_index_cases hnotOutside hlegal third k hklt hmid with
        hkp | hks
    · subst k
      exact hthirdBefore (hexAWMid_edge_injective c
        (hmid.symm.trans C.before_mid))
    · subst k
      exact hthirdAfter (hexAWMid_edge_injective c
        (hmid.symm.trans C.after_mid))
  have hfinal : hexInfra_midAccum hexAWStart 1 (ts.take k) =
      hexAWMid c endEdge := by
    rw [hkeq, List.take_length]
    rw [← hexInfra_endMid_eq_midAccum]
    exact hend
  have hthirdEnd : third = endEdge :=
    hexAWMid_edge_injective c (hmid.symm.trans hfinal)
  exact ⟨fun h => hthirdBefore (hthirdEnd.trans h),
    fun h => hthirdAfter (hthirdEnd.trans h)⟩




theorem HexEndpointLocalCrossing.endpoint_lookahead
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (endEdge : Fin 3)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3) :
    hexInfra_midAccum hexAWStart 1 ts +
      halfStep (hexInfra_headAccum 1 ts) = hexAWPos c := by
  have hendMid : hexInfra_midAccum hexAWStart 1 ts =
      hexAWMid c endEdge := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact hend
  rcases hexEndpoint_forward_vertex_of_mid ts c endEdge hlegal.1
      hendMid with hforward | hforward
  · exact hforward
  · have hnpos : 0 < ts.length :=
      lt_of_le_of_lt (Nat.zero_le C.index) C.index_lt
    have hlastLt : ts.length - 1 < ts.length := by omega
    have hedge := hexEndpoint_edge_endpoint_cases
      ts c endEdge hlegal.1 hendMid
    have hback : hexInfra_midAccum hexAWStart 1 ts -
        halfStep (hexInfra_headAccum 1 ts) = hexAWPos c := by
      rcases hedge with hedge | hedge
      · have hpos : hexAWPos (hexAWNeighbor c endEdge) = hexAWPos c :=
          hforward.symm.trans hedge.1
        exact (hexAWNeighbor_ne c endEdge (hexAWPos_injective hpos)).elim
      · exact hedge.2
    have hlastVertex :
        hexJordan_vertexPos hexAWStart 1 ts (ts.length - 1) =
          hexAWPos c := by
      have hv := hexEndpoint_vertexPos_eq_nextMid_sub
        ts (ts.length - 1) (by omega)
      have hsucc : ts.length - 1 + 1 = ts.length := by omega
      rw [hsucc, List.take_length] at hv
      exact hv.trans hback
    have hindex : ts.length - 1 = C.index := by
      by_contra hne
      exact (hexEndpoint_vertexPos_ne_of_saw ts hlegal.2
        (ts.length - 1) C.index hlastLt C.index_lt hne)
          (hlastVertex.trans C.at_vertex.symm)
    have hlen : ts.length = C.index + 1 := by omega
    have hfinalAfter : hexAWMid c endEdge = hexAWMid c C.after := by
      rw [← hendMid, ← C.after_mid, ← hlen, List.take_length]
    have := (C.endEdge_ne hnotOutside hlegal endEdge hend hcount).2
    exact (this (hexAWMid_edge_injective c hfinalAfter)).elim





theorem hexEndpoint_kTwo_last_vertex_aw
    (base : List ℤ) (t : ℤ) (c : HexAWCoord) (e : Fin 3)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 (base ++ [t])).EndpointIsLegalSAW)
    (hend : (ofTurns hexAWStart 1 (base ++ [t])).EndsAt (hexAWMid c e))
    (hneStart : hexAWMid c e ≠ hexAWStart)
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) (base ++ [t]) = 2) :
    hexInfra_midAccum hexAWStart 1 base +
      halfStep (hexInfra_headAccum 1 base) = hexAWPos c := by
  have happ := (endpointIsLegalSAW_append_one_iff
    hexAWStart 1 base t).mp hlegal
  have hfresh := hexEndpoint_final_mid_fresh_aw
    base t c e hlegal hend hneStart
  obtain ⟨f, hfe, hfBase⟩ := hexEndpoint_count_two_other_base_mid
    base t c e hend hfresh hcount
  have hendMid : hexInfra_midAccum hexAWStart 1 (base ++ [t]) =
      hexAWMid c e := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact hend
  have hmids : (ofTurns hexAWStart 1 (base ++ [t])).mids =
      (ofTurns hexAWStart 1 base).mids ++ [hexAWMid c e] := by
    change midsAux hexAWStart 1 (base ++ [t]) =
      midsAux hexAWStart 1 base ++ [hexAWMid c e]
    rw [hexCyclic_midsAux_append_single]
    rw [hexCyclic_midAccum_append_single] at hendMid
    rw [hendMid]
  have passBaseFull {z : ℂ}
      (hz : PassesThrough hexAWStart 1 base z) :
      PassesThrough hexAWStart 1 (base ++ [t]) z := by
    unfold PassesThrough at hz ⊢
    rw [hmids, List.mem_append]
    exact Or.inl hz
  have heFull : PassesThrough hexAWStart 1 (base ++ [t])
      (hexAWMid c e) :=
    hexClass_endsAt_passesThrough (base ++ [t]) (hexAWMid c e) hend
  have threeImpossible (g : Fin 3) (hgf : g ≠ f) (hge : g ≠ e)
      (hgBase : PassesThrough hexAWStart 1 base (hexAWMid c g)) : False := by
    have hfFull := passBaseFull hfBase
    have hgFull := passBaseFull hgBase
    have hall : ∀ l : Fin 3,
        PassesThrough hexAWStart 1 (base ++ [t]) (hexAWMid c l) := by
      intro l
      fin_cases e <;> fin_cases f <;> fin_cases g <;> fin_cases l <;>
        simp_all
    have hthree := hexAW_specialMidCount_three_of_all
      (base ++ [t]) c hall
    omega
  unfold PassesThrough HexWalk.mids at hfBase
  change hexAWMid c f ∈ midsAux hexAWStart 1 base at hfBase
  rw [List.mem_iff_getElem] at hfBase
  obtain ⟨k, hklist, hkget⟩ := hfBase
  have hk : k ≤ base.length := by
    rw [length_midsAux] at hklist
    omega
  have hget := hexJordan_midsAux_getElem?_eq hexAWStart 1 base k hk
  rw [List.getElem?_eq_getElem hklist, Option.some.injEq] at hget
  have hmid : hexInfra_midAccum hexAWStart 1 (base.take k) =
      hexAWMid c f := hget.symm.trans hkget
  by_cases hkzero : k = 0
  · subst k
    simp only [List.take_zero, hexInfra_midAccum_nil] at hmid
    have hedge : hexAWMid hexAWOriginCoord 0 = hexAWMid c f := by
      rw [hexAWMid_origin_zero]
      exact hmid
    rcases (hexAWMid_eq_iff hexAWOriginCoord c 0 f).mp hedge with
        ⟨hc, hf0⟩ | ⟨hc, hf0⟩
    · subst c
      subst f
      rcases base with _ | ⟨u, us⟩
      · simp [hexAWStart, halfStep, hexAWOriginCoord, hexAWPos,
          show hexUnit 4 = -hexUnit 1 by simpa using hexUnit_add_three 1]
      · have hu : u = 1 ∨ u = -1 := happ.1.1 u (by simp)
        have hstartForward : hexAWStart + halfStep 1 =
            hexAWPos hexAWOriginCoord := by
          simp [hexAWStart, halfStep, hexAWOriginCoord, hexAWPos,
            show hexUnit 4 = -hexUnit 1 by simpa using hexUnit_add_three 1]
        obtain ⟨g, hgf, hg⟩ := hexEndpoint_next_mid_of_forward_vertex
          [] u hexAWOriginCoord 0 (by simp) hu
          (by simpa using hexAWMid_origin_zero.symm) hstartForward
        have hgBase : PassesThrough hexAWStart 1 (u :: us)
            (hexAWMid hexAWOriginCoord g) := by
          have hp := hexEndpoint_prefix_mid_mem hexAWStart 1 (u :: us) 1 (by simp)
          rw [← hg]
          simpa using hp
        have hge : g ≠ e := by
          intro hge
          apply hfresh
          simpa [hge] using hgBase
        exact (threeImpossible g hgf hge hgBase).elim
    · exact (hnotOutside hc).elim
  · by_cases hklast : k = base.length
    · have hbaseMid : hexInfra_midAccum hexAWStart 1 base =
          hexAWMid c f := by
        simpa [hklast] using hmid
      rcases hexEndpoint_edge_endpoint_cases base c f happ.1.1 hbaseMid with
          hforward | hforward
      · exact hforward.1
      · rcases List.eq_nil_or_concat base with hnil | ⟨s, u, hbase⟩
        · subst base
          exact (hkzero (by simpa using hklast)).elim
        · subst base
          have hu : u = 1 ∨ u = -1 := happ.1.1 u (by simp)
          have hslegal : ∀ q ∈ s, q = 1 ∨ q = -1 := by
            intro q hq
            exact happ.1.1 q (by simp [hq])
          obtain ⟨g, hgf, hg⟩ :=
            hexEndpoint_previous_mid_of_forward_outer
              s u c f hslegal hu
                (by simpa only [List.concat_eq_append] using hbaseMid)
                (by simpa only [List.concat_eq_append] using hforward.1)
          have hgBase : PassesThrough hexAWStart 1 (s ++ [u])
              (hexAWMid c g) := by
            have hp := hexEndpoint_prefix_mid_mem
              hexAWStart 1 (s ++ [u]) s.length (by simp)
            rw [← hg]
            simpa using hp
          have hge : g ≠ e := by
            intro hge
            apply hfresh
            simpa [hge] using hgBase
          exact (threeImpossible g hgf hge
            (by simpa only [List.concat_eq_append] using hgBase)).elim
    · have hklt : k < base.length := by omega
      obtain ⟨g, hgf, hgBase⟩ :=
        hexEndpoint_internal_mid_forces_second
          base c f k (by omega) hklt happ.1.1 hmid
      have hge : g ≠ e := by
        intro hge
        apply hfresh
        simpa [hge] using hgBase
      exact (threeImpossible g hgf hge hgBase).elim





theorem hexEndpoint_count_one_forward_vertex_aw
    (ts : List ℤ) (c : HexAWCoord) (e : Fin 3)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c e))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 1) :
    hexInfra_midAccum hexAWStart 1 ts +
      halfStep (hexInfra_headAccum 1 ts) = hexAWPos c := by
  have hmid : hexInfra_midAccum hexAWStart 1 ts = hexAWMid c e := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact hend
  rcases hexEndpoint_forward_vertex_of_mid ts c e hlegal.1 hmid with
      hforward | hforward
  · exact hforward
  · rcases List.eq_nil_or_concat ts with rfl | ⟨s, t, rfl⟩
    · have hedge : hexAWMid hexAWOriginCoord 0 = hexAWMid c e :=
        hexAWMid_origin_zero.trans hmid
      rcases (hexAWMid_eq_iff hexAWOriginCoord c 0 e).mp hedge with
          ⟨hc, he⟩ | ⟨hc, he⟩
      · subst c
        subst e
        have hstartForward : hexAWStart + halfStep 1 =
            hexAWPos hexAWOriginCoord := by
          simp [hexAWStart, halfStep, hexAWOriginCoord, hexAWPos,
            show hexUnit 4 = -hexUnit 1 by
              simpa using hexUnit_add_three 1]
        have hpos : hexAWPos hexAWOriginCoord =
            hexAWPos (hexAWNeighbor hexAWOriginCoord 0) :=
          hstartForward.symm.trans hforward
        exact (hexAWNeighbor_ne hexAWOriginCoord 0
          (hexAWPos_injective hpos).symm).elim
      · exact (hnotOutside hc).elim
    · have ht : t = 1 ∨ t = -1 := hlegal.1 t (by simp)
      have hslegal : ∀ u ∈ s, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal.1 u (by simp [hu])
      obtain ⟨f, hfe, hprev⟩ :=
        hexEndpoint_previous_mid_of_forward_outer
          s t c e hslegal ht
            (by simpa only [List.concat_eq_append] using hmid)
            (by simpa only [List.concat_eq_append] using hforward)
      have hepass : PassesThrough hexAWStart 1 (s ++ [t])
          (hexAWMid c e) :=
        hexClass_endsAt_passesThrough (s ++ [t]) (hexAWMid c e)
          (by simpa only [List.concat_eq_append] using hend)
      have hfpass : PassesThrough hexAWStart 1 (s ++ [t])
          (hexAWMid c f) := by
        rw [← hprev]
        have hp := hexEndpoint_prefix_mid_mem
          hexAWStart 1 (s ++ [t]) s.length (by simp)
        simpa using hp
      have htwo := specialMidCount_ge_two_of_labels
        hexAWStart 1 (hexAWPos c)
        (hexAWMid c 0 - hexAWPos c) (s ++ [t]) e f hfe.symm
        (by simpa only [hexAW_labelMid_eq_mid] using hepass)
        (by simpa only [hexAW_labelMid_eq_mid] using hfpass)
      have hcount' : specialMidCount hexAWStart 1 (hexAWPos c)
          (hexAWMid c 0 - hexAWPos c) (s ++ [t]) = 1 := by
        simpa only [List.concat_eq_append] using hcount
      omega



def hexEndpoint_count_one_launch_aw
    (ts : List ℤ) (c : HexAWCoord) (e : Fin 3)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c e))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 1) :
    HexCyclicLaunch hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) e ts where
  endsAt := by
    simpa only [hexAW_labelMid_eq_mid] using hend
  lastVertex := by
    rw [hexAW_labelMid_eq_mid]
    have hmid : hexInfra_midAccum hexAWStart 1 ts = hexAWMid c e := by
      rw [← hexInfra_endMid_eq_midAccum]
      exact hend
    rw [← hmid]
    exact hexEndpoint_count_one_forward_vertex_aw
      ts c e hnotOutside hlegal hend hcount



theorem hexEndpoint_kTwo_mem_cyclicTriplet_aw
    {region : ℂ → Prop} (c : HexAWCoord) (e : Fin 3)
    (base : List ℤ) (t : ℤ)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hneStart : hexAWMid c e ≠ hexAWStart)
    (hvalid : (ofTurns hexAWStart 1 (base ++ [t])).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 (base ++ [t])).StaysIn region ∧
      (ofTurns hexAWStart 1 (base ++ [t])).EndsAt (hexAWMid c e))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) (base ++ [t]) = 2)
    (hall : ∀ f : Fin 3, region (hexAWMid c f)) :
    ∃ C : HexEndpointCyclicTriplet region hexAWStart 1
        (hexAWPos c) (hexAWMid c 0 - hexAWPos c),
      base ++ [t] ∈ C.piece ∧ C.base = base := by
  have hlast := hexEndpoint_kTwo_last_vertex_aw base t c e
    hnotOutside hvalid.1 hvalid.2.2 hneStart hcount
  have hnew := hexEndpoint_final_mid_fresh_aw base t c e
    hvalid.1 hvalid.2.2 hneStart
  have hvalid' :
      (ofTurns hexAWStart 1 (base ++ [t])).EndpointIsLegalSAW ∧
        (ofTurns hexAWStart 1 (base ++ [t])).StaysIn region ∧
        (ofTurns hexAWStart 1 (base ++ [t])).EndsAt
          (labelMid (hexAWPos c)
            (hexAWMid c 0 - hexAWPos c) e) := by
    simpa only [hexAW_labelMid_eq_mid] using hvalid
  have hnew' : ¬PassesThrough hexAWStart 1 base
      (labelMid (hexAWPos c) (hexAWMid c 0 - hexAWPos c) e) := by
    simpa only [hexAW_labelMid_eq_mid] using hnew
  have hall' : ∀ f : Fin 3,
      region (labelMid (hexAWPos c)
        (hexAWMid c 0 - hexAWPos c) f) := by
    intro f
    simpa only [hexAW_labelMid_eq_mid] using hall f
  exact hexEndpoint_kTwo_mem_cyclicTriplet e base t
    (hexAW_base_du_ne_zero c) hvalid' hcount hlast hnew' hall'






def hexEndpointLoopPartner : List ℤ → List ℤ
  | [] => []
  | t :: tail => (-t) :: loopReverse tail

theorem hexEndpointLoopPartner_eq_anchored (L : List ℤ) :
    hexEndpointLoopPartner L = anchoredLoopReverse L := by
  cases L <;> rfl

theorem hexEndpointLoopPartner_length_of_ne_nil (L : List ℤ)
    (hL : L ≠ []) : (hexEndpointLoopPartner L).length = L.length := by
  cases L with
  | nil => exact (hL rfl).elim
  | cons u tail => simp [hexEndpointLoopPartner, loopReverse_length]

theorem hexEndpointLoopPartner_sum
    (L : List ℤ) (hfirst : ∃ tail, L = 1 :: tail)
    (hsum : L.sum = -4) : (hexEndpointLoopPartner L).sum = 4 := by
  obtain ⟨tail, rfl⟩ := hfirst
  simp only [hexEndpointLoopPartner, List.sum_cons, loopReverse_sum] at hsum ⊢
  omega

@[simp] theorem hexEndpointLoopPartner_involutive (L : List ℤ) :
    hexEndpointLoopPartner (hexEndpointLoopPartner L) = L := by
  rw [hexEndpointLoopPartner_eq_anchored,
    hexEndpointLoopPartner_eq_anchored,
    anchoredLoopReverse_involutive]




structure HexEndpointCyclicLoopPair (region : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) where
  baseLabel : Fin 3
  base : List ℤ
  loopQ : List ℤ
  loopQ_first : ∃ tail, loopQ = 1 :: tail
  loopQ_sum : loopQ.sum = -4
  succ_valid :
    (ofTurns a h0 (base ++ loopQ)).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ loopQ)).StaysIn region ∧
      (ofTurns a h0 (base ++ loopQ)).EndsAt
        (labelMid v du (hexCyclicSucc baseLabel))
  pred_valid :
    (ofTurns a h0 (base ++ hexEndpointLoopPartner loopQ)).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ hexEndpointLoopPartner loopQ)).StaysIn region ∧
      (ofTurns a h0 (base ++ hexEndpointLoopPartner loopQ)).EndsAt
        (labelMid v du (hexCyclicPred baseLabel))

def HexEndpointCyclicLoopPair.piece
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (P : HexEndpointCyclicLoopPair region a h0 v du) : Finset (List ℤ) :=
  {P.base ++ P.loopQ, P.base ++ hexEndpointLoopPartner P.loopQ}

private theorem hexEndpoint_cyclicSucc_ne_pred (j : Fin 3) :
    hexCyclicSucc j ≠ hexCyclicPred j := by
  fin_cases j <;> decide



theorem HexEndpointCyclicLoopPair.contribution_zero
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (P : HexEndpointCyclicLoopPair region a h0 v du) :
    (labelMid v du (hexCyclicSucc P.baseLabel) - v) *
        endpointParafSummand region a h0
          (labelMid v du (hexCyclicSucc P.baseLabel))
          (5 / 8) hexChi (P.base ++ P.loopQ) +
      (labelMid v du (hexCyclicPred P.baseLabel) - v) *
        endpointParafSummand region a h0
          (labelMid v du (hexCyclicPred P.baseLabel))
          (5 / 8) hexChi
            (P.base ++ hexEndpointLoopPartner P.loopQ) = 0 := by
  let d := labelMid v du P.baseLabel - v
  have hsucc : v + hexOmega * d =
      labelMid v du (hexCyclicSucc P.baseLabel) := by
    simpa [d] using (hexCyclicSucc_mid v du P.baseLabel).symm
  have hpred : v + hexOmega ^ 2 * d =
      labelMid v du (hexCyclicPred P.baseLabel) := by
    simpa [d] using (hexCyclicPred_mid v du P.baseLabel).symm
  have hne : P.loopQ ≠ [] := by
    obtain ⟨tail, htail⟩ := P.loopQ_first
    rw [htail]
    simp
  have hz := endpoint_genuine_pair_zero
    region a h0 v d P.base P.loopQ
      (hexEndpointLoopPartner P.loopQ) P.loopQ_sum
      (hexEndpointLoopPartner_sum P.loopQ P.loopQ_first P.loopQ_sum)
      (hexEndpointLoopPartner_length_of_ne_nil P.loopQ hne).symm
      (by simpa [hsucc] using P.succ_valid)
      (by simpa [hpred] using P.pred_valid)
  simpa [hsucc, hpred] using hz

theorem HexEndpointCyclicLoopPair.sum_piece_zero
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) (P : HexEndpointCyclicLoopPair region a h0 v du) :
    ∑ ts ∈ P.piece, endpointCombinedSummand region a h0 v du ts = 0 := by
  have hne : P.base ++ P.loopQ ≠
      P.base ++ hexEndpointLoopPartner P.loopQ := by
    intro heq
    have hm : labelMid v du (hexCyclicSucc P.baseLabel) =
        labelMid v du (hexCyclicPred P.baseLabel) :=
      P.succ_valid.2.2.symm.trans (heq ▸ P.pred_valid.2.2)
    exact hexEndpoint_cyclicSucc_ne_pred P.baseLabel
      (labelMid_injective hdu hm)
  rw [show (∑ ts ∈ P.piece,
      endpointCombinedSummand region a h0 v du ts) =
      endpointCombinedSummand region a h0 v du (P.base ++ P.loopQ) +
        endpointCombinedSummand region a h0 v du
          (P.base ++ hexEndpointLoopPartner P.loopQ) by
    simp [HexEndpointCyclicLoopPair.piece, hne]]
  rw [endpointCombinedSummand_at_label hdu
      (hexCyclicSucc P.baseLabel) P.succ_valid.2.2,
    endpointCombinedSummand_at_label hdu
      (hexCyclicPred P.baseLabel) P.pred_valid.2.2]
  exact P.contribution_zero






noncomputable def hexEndpointPrefixCoord (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) (k : ℕ) : HexAWCoord :=
  Classical.choose (hexEndpoint_vertex_exists_aw (ts.take k) (by
    intro t ht
    exact hlegal t (List.mem_of_mem_take ht)))

theorem hexEndpointPrefixCoord_pos (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) (k : ℕ) :
    hexJordan_vertexPos hexAWStart 1 ts k =
      hexAWPos (hexEndpointPrefixCoord ts hlegal k) := by
  exact Classical.choose_spec (hexEndpoint_vertex_exists_aw (ts.take k) (by
    intro t ht
    exact hlegal t (List.mem_of_mem_take ht)))


theorem hexEndpointPrefixCoord_adjacent (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (k : ℕ) (hk : k < ts.length) :
    ∃ e : Fin 3,
      hexAWNeighbor (hexEndpointPrefixCoord ts hlegal k) e =
        hexEndpointPrefixCoord ts hlegal (k + 1) := by
  let ck := hexEndpointPrefixCoord ts hlegal k
  let cn := hexEndpointPrefixCoord ts hlegal (k + 1)
  have hlegalNext : ∀ t ∈ ts.take (k + 1), t = 1 ∨ t = -1 := by
    intro t ht
    exact hlegal t (List.mem_of_mem_take ht)
  have hnpos : hexInfra_midAccum hexAWStart 1 (ts.take (k + 1)) +
      halfStep (hexInfra_headAccum 1 (ts.take (k + 1))) = hexAWPos cn := by
    simpa [hexJordan_vertexPos, cn] using
      hexEndpointPrefixCoord_pos ts hlegal (k + 1)
  obtain ⟨e, hinc⟩ := hexEndpoint_mid_incident_aw
    (ts.take (k + 1)) cn hlegalNext hnpos
  have hcpos : hexInfra_midAccum hexAWStart 1 (ts.take (k + 1)) -
      halfStep (hexInfra_headAccum 1 (ts.take (k + 1))) = hexAWPos ck := by
    have hp := hexEndpoint_vertexPos_eq_nextMid_sub ts k hk
    rw [hexEndpointPrefixCoord_pos ts hlegal k] at hp
    simpa [ck] using hp.symm
  have hbackPos : hexAWPos (hexAWNeighbor cn e) = hexAWPos ck := by
    unfold hexAWMid at hinc
    linear_combination -2 * hinc + hnpos + hcpos
  have hback : hexAWNeighbor cn e = ck := hexAWPos_injective hbackPos
  refine ⟨e, ?_⟩
  have := congrArg (fun d => hexAWNeighbor d e) hback
  simpa [ck, cn] using this.symm





def HexEndpointLocalCrossing.loopLength
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c) : ℕ :=
  ts.length - C.index

theorem HexEndpointLocalCrossing.loopLength_pos
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c) : 0 < C.loopLength := by
  simpa only [HexEndpointLocalCrossing.loopLength] using
    (Nat.sub_pos_of_lt C.index_lt)



noncomputable def HexEndpointLocalCrossing.loopCoord
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (i : Fin C.loopLength) : HexAWCoord :=
  hexEndpointPrefixCoord ts hlegal (C.index + i.val)


noncomputable def HexEndpointLocalCrossing.loopCoords
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) : List HexAWCoord :=
  List.ofFn (C.loopCoord hlegal)

@[simp] theorem HexEndpointLocalCrossing.loopCoords_length
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    (C.loopCoords hlegal).length = C.loopLength := by
  simp [HexEndpointLocalCrossing.loopCoords]



theorem HexEndpointLocalCrossing.loopCoord_injective
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW) :
    Function.Injective (C.loopCoord hlegal.1) := by
  intro i j hij
  apply Fin.ext
  by_contra hval
  have hi : C.index + i.val < ts.length := by
    have := i.isLt
    simp only [HexEndpointLocalCrossing.loopLength] at this
    omega
  have hj : C.index + j.val < ts.length := by
    have := j.isLt
    simp only [HexEndpointLocalCrossing.loopLength] at this
    omega
  have hindex : C.index + i.val ≠ C.index + j.val := by omega
  have hpos := congrArg hexAWPos hij
  simp only [HexEndpointLocalCrossing.loopCoord] at hpos
  rw [← hexEndpointPrefixCoord_pos ts hlegal.1 (C.index + i.val),
    ← hexEndpointPrefixCoord_pos ts hlegal.1 (C.index + j.val)] at hpos
  exact (hexEndpoint_vertexPos_ne_of_saw ts hlegal.2
    (C.index + i.val) (C.index + j.val) hi hj hindex) hpos

theorem HexEndpointLocalCrossing.loopCoords_nodup
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW) :
    (C.loopCoords hlegal.1).Nodup := by
  rw [HexEndpointLocalCrossing.loopCoords, List.nodup_ofFn]
  exact C.loopCoord_injective hlegal


theorem HexEndpointLocalCrossing.loopCoord_zero
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    [NeZero C.loopLength] :
    C.loopCoord hlegal 0 = c := by
  apply hexAWPos_injective
  rw [← C.at_vertex]
  simpa [HexEndpointLocalCrossing.loopCoord, hexJordan_vertexPos] using
    (hexEndpointPrefixCoord_pos ts hlegal C.index).symm


theorem HexEndpointLocalCrossing.finalPrefixCoord_eq
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (endEdge : Fin 3)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3) :
    hexEndpointPrefixCoord ts hlegal.1 ts.length = c := by
  apply hexAWPos_injective
  rw [← C.endpoint_lookahead hnotOutside hlegal endEdge hend hcount]
  simpa [hexJordan_vertexPos] using
    (hexEndpointPrefixCoord_pos ts hlegal.1 ts.length).symm



theorem HexEndpointLocalCrossing.loopCoord_cyclic_adjacent
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (endEdge : Fin 3)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3)
    [NeZero C.loopLength] (i : Fin C.loopLength) :
    ∃ e : Fin 3,
      hexAWNeighbor (C.loopCoord hlegal.1 i) e =
        C.loopCoord hlegal.1 (i + 1) := by
  by_cases hnext : i.val + 1 < C.loopLength
  · have hk : C.index + i.val < ts.length := by
      have := i.isLt
      simp only [HexEndpointLocalCrossing.loopLength] at this hnext
      omega
    obtain ⟨e, he⟩ := hexEndpointPrefixCoord_adjacent ts hlegal.1
      (C.index + i.val) hk
    have hi1 : (i + 1 : Fin C.loopLength) =
        ⟨i.val + 1, hnext⟩ := by
      apply Fin.ext
      rw [Fin.val_add, Fin.val_one',
        Nat.mod_eq_of_lt (show 1 < C.loopLength by omega),
        Nat.mod_eq_of_lt hnext]
    refine ⟨e, ?_⟩
    rw [hi1]
    simpa [HexEndpointLocalCrossing.loopCoord, Nat.add_assoc] using he
  · have hwrap : i.val + 1 = C.loopLength := by omega
    have hk : C.index + i.val < ts.length := by
      simp only [HexEndpointLocalCrossing.loopLength] at hwrap
      omega
    have hkEnd : C.index + i.val + 1 = ts.length := by
      simp only [HexEndpointLocalCrossing.loopLength] at hwrap
      omega
    obtain ⟨e, he⟩ := hexEndpointPrefixCoord_adjacent ts hlegal.1
      (C.index + i.val) hk
    have hi1 : (i + 1 : Fin C.loopLength) = 0 := by
      apply Fin.ext
      rw [Fin.val_zero, Fin.val_add, Fin.val_one']
      by_cases hOne : C.loopLength = 1
      · simp [hOne]
        exact Nat.mod_one i.val
      · have hOneLt : 1 < C.loopLength := by
          have := C.loopLength_pos
          omega
        rw [Nat.mod_eq_of_lt hOneLt, hwrap, Nat.mod_self]
    refine ⟨e, ?_⟩
    calc
      hexAWNeighbor (C.loopCoord hlegal.1 i) e =
          hexEndpointPrefixCoord ts hlegal.1 ts.length := by
            simpa [HexEndpointLocalCrossing.loopCoord, hkEnd] using he
      _ = c := C.finalPrefixCoord_eq
        hnotOutside hlegal endEdge hend hcount
      _ = C.loopCoord hlegal.1 (i + 1) := by
        rw [hi1]
        exact (C.loopCoord_zero hlegal.1).symm

end

end StatMech.Universality

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.Universality.HexLiteralHWAugment
import Code.Universality.HexCorrectedStripLimits

namespace StatMech.Universality

open HexWalk

noncomputable section




noncomputable def hlhr_stripColumnRealization_zero (ts : List ℤ)
    (hleg : (ofTurns 0 0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace 0 ts) :
    HLHRStripColumnRealization 0 ts hhalf where
  column := fun p _ => hlhr_latticeWidth ts p
  column_pos := by
    intro p hp
    apply hlhr_latticeWidth_pos_of_span_pos ts hleg.1 p
    exact hlhr_literalSpans_pos 0 ts hhalf
      (hlhr_intervalSpan (hlhr_height 0 ts) p) (by
        simpa [hlhr_literalSpans, hlhr_intervalSpans] using
          List.mem_map_of_mem hp)
  span_strict := by
    intro p _ q _ hpq
    exact hlhr_latticeWidth_gt_of_span_gt ts hleg.1 p q hpq

@[simp] theorem hlhr_stripColumnRealization_zero_column (ts : List ℤ)
    (hleg : (ofTurns 0 0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace 0 ts)
    (p : ℕ × ℕ) (hp : p ∈ hlhr_literalIntervals 0 ts) :
    (hlhr_stripColumnRealization_zero ts hleg hhalf).column p hp =
      hlhr_latticeWidth ts p := rfl



theorem hlhr_literalBridge_mem_with_column (ts : List ℤ)
    (hleg : (ofTurns 0 0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace 0 ts)
    (b : HexBridge) (hb : b ∈ hlhr_literalBridgeList ts hleg hhalf) :
    ∃ p : {p // p ∈ hlhr_literalIntervals 0 ts},
      b = hlhr_literalBridge ts hleg hhalf p ∧
        b.width = (hlhr_stripColumnRealization_zero ts hleg hhalf).column p.1 p.2 := by
  unfold hlhr_literalBridgeList at hb
  rw [List.mem_map] at hb
  obtain ⟨p, hp, rfl⟩ := hb
  exact ⟨p, rfl, rfl⟩




def hlhc_coordBound (c : HexAWCoord) : ℕ :=
  c.i.natAbs + c.j.natAbs

theorem hlhc_coord_le_bound_i (c : HexAWCoord) :
    c.i ≤ (hlhc_coordBound c : ℕ) := by
  rcases c with ⟨i, j, color⟩
  have hj : (0 : ℤ) ≤ |j| := abs_nonneg j
  cases i <;> simp [hlhc_coordBound] <;> omega

theorem hlhc_coord_le_bound_j (c : HexAWCoord) :
    c.j ≤ (hlhc_coordBound c : ℕ) := by
  rcases c with ⟨i, j, color⟩
  have hi : (0 : ℤ) ≤ |i| := abs_nonneg i
  cases j <;> simp [hlhc_coordBound] <;> omega




noncomputable def hlhc_prefixCoord (ts : List ℤ)
    (hlegal : (ofTurns hexAWStart 1 ts).LegalTurns) (k : ℕ) : HexAWCoord := by
  have htake : ∀ t ∈ ts.take k, t = 1 ∨ t = -1 := by
    intro t ht
    exact hlegal t (List.mem_of_mem_take ht)
  exact Classical.choose (hexEndpoint_vertex_exists_aw (ts.take k) htake)

theorem hlhc_prefixCoord_vertex (ts : List ℤ)
    (hlegal : (ofTurns hexAWStart 1 ts).LegalTurns) (k : ℕ) :
    hexInfra_midAccum hexAWStart 1 (ts.take k) +
        halfStep (hexInfra_headAccum 1 (ts.take k)) =
      hexAWPos (hlhc_prefixCoord ts hlegal k) := by
  unfold hlhc_prefixCoord
  exact Classical.choose_spec (hexEndpoint_vertex_exists_aw (ts.take k)
    (by
      intro t ht
      exact hlegal t (List.mem_of_mem_take ht)))

theorem hlhc_prefixCoord_mid_incident (ts : List ℤ)
    (hlegal : (ofTurns hexAWStart 1 ts).LegalTurns) (k : ℕ) :
    ∃ e : Fin 3,
      hexInfra_midAccum hexAWStart 1 (ts.take k) =
        hexAWMid (hlhc_prefixCoord ts hlegal k) e := by
  apply hexEndpoint_mid_incident_aw
  · intro t ht
    exact hlegal t (List.mem_of_mem_take ht)
  · exact hlhc_prefixCoord_vertex ts hlegal k





structure HLHCCanonicalColumnWalk (T : ℕ) (ts : List ℤ) where
  legal : (ofTurns hexAWStart 1 ts).IsLegalSAW
  horizontal : ∀ k, k < ts.length →
    0 ≤ hexAWBookRe2 (hlhc_prefixCoord ts legal.1 k) ∧
      hexAWBookRe2 (hlhc_prefixCoord ts legal.1 k) ≤ 3 * T
  topCoord : HexAWCoord
  top_white : topCoord.color = .white
  top_depth : hexAWDepth topCoord = T
  endsAt : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid topCoord 0)



noncomputable def HLHCCanonicalColumnWalk.stripHeight
    {T : ℕ} {ts : List ℤ} (W : HLHCCanonicalColumnWalk T ts) : ℕ :=
  max ((Finset.range ts.length).sup
      (fun k => hlhc_coordBound (hlhc_prefixCoord ts W.legal.1 k)))
    (hlhc_coordBound W.topCoord)

theorem HLHCCanonicalColumnWalk.prefix_mem_vertexSet
    {T : ℕ} {ts : List ℤ} (W : HLHCCanonicalColumnWalk T ts)
    {k : ℕ} (hk : k < ts.length) :
    hlhc_prefixCoord ts W.legal.1 k ∈
      hexCSVertexSet T W.stripHeight := by
  rw [hexCS_mem_vertexSet_iff]
  refine ⟨(W.horizontal k hk).1, (W.horizontal k hk).2, ?_, ?_⟩
  · exact le_trans (hlhc_coord_le_bound_i _)
      (by
        exact_mod_cast le_trans
          (Finset.le_sup (f := fun n =>
            hlhc_coordBound (hlhc_prefixCoord ts W.legal.1 n))
            (Finset.mem_range.mpr hk))
          (Nat.le_max_left _ _))
  · exact le_trans (hlhc_coord_le_bound_j _)
      (by
        exact_mod_cast le_trans
          (Finset.le_sup (f := fun n =>
            hlhc_coordBound (hlhc_prefixCoord ts W.legal.1 n))
            (Finset.mem_range.mpr hk))
          (Nat.le_max_left _ _))

theorem HLHCCanonicalColumnWalk.top_mem_vertexSet
    {T : ℕ} {ts : List ℤ} (W : HLHCCanonicalColumnWalk T ts)
    (hT : 0 < T) :
    W.topCoord ∈ hexCSVertexSet T W.stripHeight := by
  rw [hexCS_mem_vertexSet_iff]
  have hbook : hexAWBookRe2 W.topCoord = 3 * T - 1 := by
    simp [hexAWBookRe2, W.top_white, W.top_depth]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hbook]
    omega
  · rw [hbook]
    omega
  · exact le_trans (hlhc_coord_le_bound_i _)
      (by exact_mod_cast Nat.le_max_right _ _)
  · exact le_trans (hlhc_coord_le_bound_j _)
      (by exact_mod_cast Nat.le_max_right _ _)

theorem HexWalk.IsLegalSAW.endpointIsLegalSAW {w : HexWalk}
    (h : w.IsLegalSAW) : w.EndpointIsLegalSAW := by
  exact ⟨h.1, List.Nodup.sublist (List.dropLast_sublist _) h.2⟩




theorem HLHCCanonicalColumnWalk.mem_topAtWidth
    {T : ℕ} {ts : List ℤ} (W : HLHCCanonicalColumnWalk T ts)
    (hT : 0 < T) : HexCSTopWalkAtWidth T hT ts := by
  refine ⟨W.stripHeight, W.legal.endpointIsLegalSAW, ?_,
    W.topCoord, W.top_mem_vertexSet hT, W.top_white, W.top_depth, W.endsAt⟩
  intro z hz
  unfold HexWalk.mids at hz
  change z ∈ midsAux hexAWStart 1 ts at hz
  rw [List.mem_iff_getElem] at hz
  obtain ⟨k, hklen, hkz⟩ := hz
  have hkle : k ≤ ts.length := by
    rw [length_midsAux] at hklen
    omega
  have hget := hexJordan_midsAux_getElem?_eq hexAWStart 1 ts k hkle
  rw [List.getElem?_eq_getElem hklen, Option.some.injEq] at hget
  have hmid : hexInfra_midAccum hexAWStart 1 (ts.take k) = z :=
    hget.symm.trans hkz
  change z ∈ hexCSMids T W.stripHeight
  by_cases hk : k < ts.length
  · obtain ⟨e, he⟩ := hlhc_prefixCoord_mid_incident ts W.legal.1 k
    rw [← hmid] 
    rw [hexCSMids, Finset.mem_biUnion]
    refine ⟨⟨hlhc_prefixCoord ts W.legal.1 k,
      W.prefix_mem_vertexSet hk⟩, Finset.mem_univ _, ?_⟩
    rw [Finset.mem_image]
    exact ⟨e, Finset.mem_univ _, he.symm⟩
  · have hkeq : k = ts.length := by omega
    have hzTop : z = hexAWMid W.topCoord 0 := by
      rw [← hmid, hkeq, List.take_length]
      rw [← hexInfra_endMid_eq_midAccum hexAWStart 1 ts]
      exact W.endsAt
    rw [hzTop, hexCSMids, Finset.mem_biUnion]
    refine ⟨⟨W.topCoord, W.top_mem_vertexSet hT⟩,
      Finset.mem_univ _, ?_⟩
    rw [Finset.mem_image]
    exact ⟨0, Finset.mem_univ _, rfl⟩






structure HLHCMidpointColumnWalk (T : ℕ) (ts : List ℤ) where
  legal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW
  midCoord : Fin ts.length → HexAWCoord
  midEdge : Fin ts.length → Fin 3
  incident : ∀ k : Fin ts.length,
    hexInfra_midAccum hexAWStart 1 (ts.take k.1) =
      hexAWMid (midCoord k) (midEdge k)
  horizontal : ∀ k : Fin ts.length,
    0 ≤ hexAWBookRe2 (midCoord k) ∧
      hexAWBookRe2 (midCoord k) ≤ 3 * T
  topCoord : HexAWCoord
  top_white : topCoord.color = .white
  top_depth : hexAWDepth topCoord = T
  endsAt : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid topCoord 0)

noncomputable def HLHCMidpointColumnWalk.stripHeight
    {T : ℕ} {ts : List ℤ} (W : HLHCMidpointColumnWalk T ts) : ℕ :=
  max (Finset.univ.sup (fun k : Fin ts.length =>
      hlhc_coordBound (W.midCoord k)))
    (hlhc_coordBound W.topCoord)

theorem HLHCMidpointColumnWalk.midCoord_mem_vertexSet
    {T : ℕ} {ts : List ℤ} (W : HLHCMidpointColumnWalk T ts)
    (k : Fin ts.length) :
    W.midCoord k ∈ hexCSVertexSet T W.stripHeight := by
  rw [hexCS_mem_vertexSet_iff]
  refine ⟨(W.horizontal k).1, (W.horizontal k).2, ?_, ?_⟩
  · exact le_trans (hlhc_coord_le_bound_i _)
      (by
        exact_mod_cast le_trans
          (Finset.le_sup (f := fun n : Fin ts.length =>
            hlhc_coordBound (W.midCoord n)) (Finset.mem_univ k))
          (Nat.le_max_left _ _))
  · exact le_trans (hlhc_coord_le_bound_j _)
      (by
        exact_mod_cast le_trans
          (Finset.le_sup (f := fun n : Fin ts.length =>
            hlhc_coordBound (W.midCoord n)) (Finset.mem_univ k))
          (Nat.le_max_left _ _))

theorem HLHCMidpointColumnWalk.top_mem_vertexSet
    {T : ℕ} {ts : List ℤ} (W : HLHCMidpointColumnWalk T ts)
    (hT : 0 < T) :
    W.topCoord ∈ hexCSVertexSet T W.stripHeight := by
  rw [hexCS_mem_vertexSet_iff]
  have hbook : hexAWBookRe2 W.topCoord = 3 * T - 1 := by
    simp [hexAWBookRe2, W.top_white, W.top_depth]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hbook]
    omega
  · rw [hbook]
    omega
  · exact le_trans (hlhc_coord_le_bound_i _)
      (by exact_mod_cast Nat.le_max_right _ _)
  · exact le_trans (hlhc_coord_le_bound_j _)
      (by exact_mod_cast Nat.le_max_right _ _)



theorem HLHCMidpointColumnWalk.mem_topAtWidth
    {T : ℕ} {ts : List ℤ} (W : HLHCMidpointColumnWalk T ts)
    (hT : 0 < T) : HexCSTopWalkAtWidth T hT ts := by
  refine ⟨W.stripHeight, W.legal, ?_,
    W.topCoord, W.top_mem_vertexSet hT, W.top_white, W.top_depth, W.endsAt⟩
  intro z hz
  unfold HexWalk.mids at hz
  change z ∈ midsAux hexAWStart 1 ts at hz
  rw [List.mem_iff_getElem] at hz
  obtain ⟨k, hklen, hkz⟩ := hz
  have hkle : k ≤ ts.length := by
    rw [length_midsAux] at hklen
    omega
  have hget := hexJordan_midsAux_getElem?_eq hexAWStart 1 ts k hkle
  rw [List.getElem?_eq_getElem hklen, Option.some.injEq] at hget
  have hmid : hexInfra_midAccum hexAWStart 1 (ts.take k) = z :=
    hget.symm.trans hkz
  change z ∈ hexCSMids T W.stripHeight
  by_cases hk : k < ts.length
  · let k' : Fin ts.length := ⟨k, hk⟩
    rw [← hmid, W.incident k', hexCSMids, Finset.mem_biUnion]
    refine ⟨⟨W.midCoord k', W.midCoord_mem_vertexSet k'⟩,
      Finset.mem_univ _, ?_⟩
    rw [Finset.mem_image]
    exact ⟨W.midEdge k', Finset.mem_univ _, rfl⟩
  · have hkeq : k = ts.length := by omega
    have hzTop : z = hexAWMid W.topCoord 0 := by
      rw [← hmid, hkeq, List.take_length]
      rw [← hexInfra_endMid_eq_midAccum hexAWStart 1 ts]
      exact W.endsAt
    rw [hzTop, hexCSMids, Finset.mem_biUnion]
    refine ⟨⟨W.topCoord, W.top_mem_vertexSet hT⟩,
      Finset.mem_univ _, ?_⟩
    rw [Finset.mem_image]
    exact ⟨0, Finset.mem_univ _, rfl⟩

end

end StatMech.Universality

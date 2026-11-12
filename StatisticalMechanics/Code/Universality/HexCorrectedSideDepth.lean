/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Universality.HexCorrectedHighestCut
import Code.Universality.HexCorrectedStripWindow
import Code.Universality.HexLiteralHWDepthCutBounds

namespace StatMech.Universality

open HexWalk

noncomputable section



structure HexCSNewSideDepthData (T : ℕ) (ts : List ℤ) where
  legal : (ofTurns hexAWStart 1 ts).IsLegalSAW
  physical_book_nonneg : ∀ k, k < ts.length →
    0 ≤ hexAWBookRe2 (hlhc_prefixCoord ts legal.1 k)
  depth_nonneg : ∀ k, k ≤ ts.length → 0 ≤ hlhd_depth ts legal k
  terminal_depth_zero : hlhd_depth ts legal ts.length = 0
  terminal_white : (hlhc_prefixCoord ts legal.1 ts.length).color = .white
  cut_depth :
    hlhd_depth ts legal (hlhda_cutPos ts legal) = (T + 1 : ℤ)



noncomputable def hexCSNewSideDepthData
    (T : ℕ) (hT : 1 ≤ T)
    (d : {ts : List ℤ // HexCSNewSideWalk T hT ts}) :
    HexCSNewSideDepthData T d.1 := by
  let L := d.2.1.choose
  have hside : HexCSSideWalk (T + 1) L (by omega) d.1 :=
    d.2.1.choose_spec
  have hendpoint := hside.1
  have hstay := hside.2.1
  let c := hside.2.2.choose
  have hcdata := hside.2.2.choose_spec
  have hc : c ∈ hexCSVertexSet (T + 1) L := hcdata.1
  have hblack : c.color = .black := hcdata.2.1
  have hcdepth : hexAWDepth c = 0 := hcdata.2.2.1
  have hcne : hexAWMid c 0 ≠ hexAWStart := hcdata.2.2.2.1
  have hend : (ofTurns hexAWStart 1 d.1).EndsAt (hexAWMid c 0) :=
    hcdata.2.2.2.2
  let e : HexCSIncidence (T + 1) L := ⟨⟨c, hc⟩, 0⟩
  have he : e ∈ hexCSBoundaryIncidences (T + 1) L := by
    apply hexCS_mem_boundary_of_classification
    left
    refine ⟨?_, ?_, ?_⟩
    · simpa [e] using hblack
    · rfl
    · simpa [e] using hcdepth
  have hene : e ≠ hexCSStartIncidence (T + 1) L (by omega) := by
    intro heq
    apply hcne
    have hm := congrArg
      (fun q : HexCSIncidence (T + 1) L =>
        hexAWMid q.vtx.1 q.edge) heq
    simpa [e] using hm
  have hadm : (ofTurns hexAWStart 1 d.1).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 d.1).StaysIn
        (hexCSFiniteRegion (T + 1) L (by omega)).inRegion ∧
      (ofTurns hexAWStart 1 d.1).EndsAt
        (hexAWMid e.vtx.1 e.edge) := by
    simpa [e] using And.intro hendpoint (And.intro hstay hend)
  have hfull : (ofTurns hexAWStart 1 d.1).IsLegalSAW :=
    ⟨hendpoint.1, hexCS_full_isSAW e d.1 he hene hadm⟩
  have hneTurns : d.1 ≠ [] := by
    intro hnil
    have hend' := hend
    rw [hnil] at hend'
    apply hcne
    have hm : hexAWStart = hexAWMid c 0 := by
      simpa [HexWalk.EndsAt, hexInfra_endMid_eq_midAccum] using hend'
    exact hm.symm
  have hfinal : hlhc_prefixCoord d.1 hfull.1 d.1.length =
      hexAWNeighbor c 0 := by
    rw [hlhc_prefixCoord_eq_endpointPrefixCoord d.1 hfull d.1.length]
    simpa [e] using
      (hexCS_finalPrefixCoord_eq_outside e d.1 he hene hadm)
  have hterminalDepth : hlhd_depth d.1 hfull d.1.length = 0 := by
    unfold hlhd_depth
    rw [hfinal, hlhda_depth_neighbor_zero, hcdepth]
  have hterminalWhite :
      (hlhc_prefixCoord d.1 hfull.1 d.1.length).color = .white := by
    rw [hfinal]
    exact hlhda_neighbor_color_black hblack rfl
  have hbookNonneg : ∀ k, k < d.1.length →
      0 ≤ hexAWBookRe2 (hlhc_prefixCoord d.1 hfull.1 k) := by
    intro k hk
    have hmem := hexCS_prefixCoord_mem d.1 ⟨hendpoint, hstay⟩ k hk
    rw [← hlhc_prefixCoord_eq_endpointPrefixCoord d.1 hfull k,
      hexCS_mem_vertexSet_iff] at hmem
    exact hmem.1
  have hdepthNonneg : ∀ k, k ≤ d.1.length →
      0 ≤ hlhd_depth d.1 hfull k := by
    intro k hk
    by_cases hlast : k = d.1.length
    · subst k
      rw [hterminalDepth]
    · have hklt : k < d.1.length := by omega
      have hbook := hbookNonneg k hklt
      change 0 ≤ hexAWDepth (hlhc_prefixCoord d.1 hfull.1 k)
      cases hcolor : (hlhc_prefixCoord d.1 hfull.1 k).color <;>
        simp [hexAWBookRe2, hcolor] at hbook ⊢ <;> omega
  let cp := hlhda_cutPos d.1 hfull
  let M := hlhd_depth d.1 hfull cp
  have hcpPos : 0 < cp := hlhda_cutPos_pos hfull hneTurns
  have hcpLe : cp ≤ d.1.length := hlhda_cutPos_le d.1 hfull
  have hMpos : 0 < M := by
    have hfirst := hlhda_cutPos_first d.1 hfull 0 hcpPos
    change hlhd_depth d.1 hfull 0 < M at hfirst
    rw [hlhda_depth_zero] at hfirst
    exact hfirst
  have hcpLt : cp < d.1.length := by
    by_contra hnot
    have hcpeq : cp = d.1.length := by omega
    have hz := hterminalDepth
    rw [← hcpeq] at hz
    change M = 0 at hz
    omega
  have hcutWhite : (hlhc_prefixCoord d.1 hfull.1 cp).color = .white := by
    have hlocal := (hlhda_cut_local hfull hneTurns).2.1
    change (hlhc_prefixCoord d.1 hfull.1 cp).color = .white at hlocal
    exact hlocal
  have hMupper : M ≤ T + 1 := by
    have hmem := hexCS_prefixCoord_mem d.1 ⟨hendpoint, hstay⟩ cp hcpLt
    rw [← hlhc_prefixCoord_eq_endpointPrefixCoord d.1 hfull cp,
      hexCS_mem_vertexSet_iff] at hmem
    change 0 ≤ hexAWBookRe2 (hlhc_prefixCoord d.1 hfull.1 cp) ∧
      hexAWBookRe2 (hlhc_prefixCoord d.1 hfull.1 cp) ≤ 3 * (T + 1) ∧
      _ at hmem
    have hbook :
        hexAWBookRe2 (hlhc_prefixCoord d.1 hfull.1 cp) = 3 * M - 1 := by
      simp [hexAWBookRe2, hcutWhite, M, hlhd_depth]
      ring
    rw [hbook] at hmem
    omega
  have hMlower : (T : ℤ) < M := by
    by_contra hnot
    have hMle : M ≤ T := by omega
    have hprefixOld : ∀ k, k < d.1.length →
        hlhc_prefixCoord d.1 hfull.1 k ∈ hexCSVertexSet T L := by
      intro k hk
      have hmem := hexCS_prefixCoord_mem d.1 ⟨hendpoint, hstay⟩ k hk
      rw [← hlhc_prefixCoord_eq_endpointPrefixCoord d.1 hfull k,
        hexCS_mem_vertexSet_iff] at hmem
      rw [hexCS_mem_vertexSet_iff]
      change 0 ≤ hexAWBookRe2 (hlhc_prefixCoord d.1 hfull.1 k) ∧
          hexAWBookRe2 (hlhc_prefixCoord d.1 hfull.1 k) ≤ 3 * T ∧
          (hlhc_prefixCoord d.1 hfull.1 k).i ≤ L ∧
          (hlhc_prefixCoord d.1 hfull.1 k).j ≤ L
      change 0 ≤ hexAWBookRe2 (hlhc_prefixCoord d.1 hfull.1 k) ∧
          hexAWBookRe2 (hlhc_prefixCoord d.1 hfull.1 k) ≤ 3 * (T + 1) ∧
          (hlhc_prefixCoord d.1 hfull.1 k).i ≤ L ∧
          (hlhc_prefixCoord d.1 hfull.1 k).j ≤ L at hmem
      have hbounds : ∀ j, j ≤ d.1.length →
          0 ≤ hlhd_depth d.1 hfull j ∧
            hlhd_depth d.1 hfull j ≤ T := by
        intro j hj
        have hmax := hlhda_cutPos_max d.1 hfull j hj
        change hlhd_depth d.1 hfull j ≤ M at hmax
        exact ⟨hdepthNonneg j hj, by omega⟩
      have hbook := hlhda_physical_book_bounds d.1 hfull T
        (by omega) hbounds hk
      exact ⟨hbook.1, hbook.2, hmem.2.2.1, hmem.2.2.2⟩
    have hcOld : c ∈ hexCSVertexSet T L := by
      rw [hexCS_mem_vertexSet_iff] at hc ⊢
      change 0 ≤ hexAWBookRe2 c ∧ hexAWBookRe2 c ≤ 3 * (T + 1) ∧
          c.i ≤ L ∧ c.j ≤ L at hc
      change 0 ≤ hexAWBookRe2 c ∧ hexAWBookRe2 c ≤ 3 * T ∧
          c.i ≤ L ∧ c.j ≤ L
      have hbook : hexAWBookRe2 c = 1 := by
        simp [hexAWBookRe2, hblack, hcdepth]
      exact ⟨by rw [hbook]; omega, by rw [hbook]; omega,
        hc.2.2.1, hc.2.2.2⟩
    have hstayOld : (ofTurns hexAWStart 1 d.1).StaysIn
        (hexCSFiniteRegion T L (by omega)).inRegion := by
      intro z hz
      unfold HexWalk.mids at hz
      change z ∈ midsAux hexAWStart 1 d.1 at hz
      rw [List.mem_iff_getElem] at hz
      obtain ⟨k, hklen, hkz⟩ := hz
      have hkle : k ≤ d.1.length := by
        rw [length_midsAux] at hklen
        omega
      have hget := hexJordan_midsAux_getElem?_eq
        hexAWStart 1 d.1 k hkle
      rw [List.getElem?_eq_getElem hklen, Option.some.injEq] at hget
      have hmid : hexInfra_midAccum hexAWStart 1 (d.1.take k) = z :=
        hget.symm.trans hkz
      change z ∈ hexCSMids T L
      by_cases hk : k < d.1.length
      · obtain ⟨edge, hedge⟩ :=
          hlhc_prefixCoord_mid_incident d.1 hfull.1 k
        rw [← hmid, hexCSMids, Finset.mem_biUnion]
        refine ⟨⟨hlhc_prefixCoord d.1 hfull.1 k, hprefixOld k hk⟩,
          Finset.mem_univ _, ?_⟩
        rw [Finset.mem_image]
        exact ⟨edge, Finset.mem_univ _, hedge.symm⟩
      · have hkeq : k = d.1.length := by omega
        have hzEnd : z = hexAWMid c 0 := by
          rw [← hmid, hkeq, List.take_length]
          rw [← hexInfra_endMid_eq_midAccum hexAWStart 1 d.1]
          exact hend
        rw [hzEnd, hexCSMids, Finset.mem_biUnion]
        refine ⟨⟨c, hcOld⟩, Finset.mem_univ _, ?_⟩
        rw [Finset.mem_image]
        exact ⟨0, Finset.mem_univ _, rfl⟩
    have hsideOld : HexCSSideWalk T L (by omega) d.1 :=
      ⟨hendpoint, hstayOld, c, hcOld, hblack, hcdepth, hcne, hend⟩
    exact (d.2.2 ⟨L, hsideOld⟩).elim
  have hcutDepth : M = (T + 1 : ℤ) := by omega
  exact
    { legal := hfull
      physical_book_nonneg := hbookNonneg
      depth_nonneg := hdepthNonneg
      terminal_depth_zero := hterminalDepth
      terminal_white := hterminalWhite
      cut_depth := by simpa [M, cp] using hcutDepth }

end

end StatMech.Universality

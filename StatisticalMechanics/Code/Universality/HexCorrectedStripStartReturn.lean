/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Universality.HexCorrectedStripAssembly

namespace StatMech.Universality

open Complex HexWalk

noncomputable section


def hexCSOutsideStartCoord : HexAWCoord := ⟨0, 0, .white⟩

@[simp] theorem hexCSOutsideStart_eq_neighbor :
    hexCSOutsideStartCoord = hexAWNeighbor hexAWOriginCoord 0 := by
  rfl

@[simp] theorem hexCSOutsideStart_mid_zero :
    hexAWMid hexCSOutsideStartCoord 0 = hexAWStart := by
  rw [hexCSOutsideStart_eq_neighbor, hexAWMid_neighbor,
    hexAWMid_origin_zero]

@[simp] theorem hexCSOutsideStart_pos :
    hexAWPos hexCSOutsideStartCoord = hexUnit 4 := by
  simp [hexCSOutsideStartCoord, hexAWPos, hexAWAxis]



theorem hexCSOutsideStart_mid_mem_iff
    (T L : ℕ) (hT : 0 < T) (e : Fin 3) :
    hexAWMid hexCSOutsideStartCoord e ∈ hexCSMids T L ↔ e = 0 := by
  constructor
  · intro hm
    fin_cases e
    · rfl
    · exfalso
      rw [hexCSMids, Finset.mem_biUnion] at hm
      obtain ⟨c, _, hc⟩ := hm
      rw [Finset.mem_image] at hc
      obtain ⟨f, _, hf⟩ := hc
      have hedge := (hexAWMid_eq_iff hexCSOutsideStartCoord c.1 1 f).mp hf.symm
      rcases hedge with ⟨hcoord, _⟩ | ⟨hcoord, _⟩
      · have hmem := c.2
        rw [hcoord, hexCS_mem_vertexSet_iff] at hmem
        simp [hexCSOutsideStartCoord, hexCSInStrip, hexAWBookRe2,
          hexAWDepth, hexAWLong] at hmem
      · have hmem := c.2
        rw [hcoord, hexCS_mem_vertexSet_iff] at hmem
        simp [hexCSOutsideStartCoord, hexAWNeighbor, hexCSInStrip,
          hexAWBookRe2, hexAWDepth, hexAWLong] at hmem
    · exfalso
      rw [hexCSMids, Finset.mem_biUnion] at hm
      obtain ⟨c, _, hc⟩ := hm
      rw [Finset.mem_image] at hc
      obtain ⟨f, _, hf⟩ := hc
      have hedge := (hexAWMid_eq_iff hexCSOutsideStartCoord c.1 2 f).mp hf.symm
      rcases hedge with ⟨hcoord, _⟩ | ⟨hcoord, _⟩
      · have hmem := c.2
        rw [hcoord, hexCS_mem_vertexSet_iff] at hmem
        simp [hexCSOutsideStartCoord, hexCSInStrip, hexAWBookRe2,
          hexAWDepth, hexAWLong] at hmem
      · have hmem := c.2
        rw [hcoord, hexCS_mem_vertexSet_iff] at hmem
        simp [hexCSOutsideStartCoord, hexAWNeighbor, hexCSInStrip,
          hexAWBookRe2, hexAWDepth, hexAWLong] at hmem
  · rintro rfl
    rw [hexCSOutsideStart_mid_zero]
    exact hexAWStart_mem_hexCSMids T L hT



theorem hexCS_endpoint_return_eq_nil
    (T L : ℕ) (hT : 0 < T) (ts : List ℤ)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt hexAWStart) :
    ts = [] := by
  induction ts using List.reverseRecOn with
  | nil => rfl
  | append_singleton base t _ =>
      exfalso
      have happ := (endpointIsLegalSAW_append_one_iff
        hexAWStart 1 base t).mp hadm.1
      have ht := happ.2
      have hendMid : hexInfra_midAccum hexAWStart 1 (base ++ [t]) =
          hexAWStart := by
        rw [← hexInfra_endMid_eq_midAccum]
        exact hadm.2.2
      rcases hexReturning_finalDirection_parallel hexAWStart 1
        (base ++ [t]) hadm.1.1 hadm.2.2 with hsame | hopp
      · have hlast : hexInfra_midAccum hexAWStart 1 base +
            halfStep (hexInfra_headAccum 1 base) =
          hexAWPos hexCSOutsideStartCoord := by
          rw [hexCyclic_midAccum_append_single] at hendMid
          rw [hexCSOutsideStart_pos]
          have hstart : hexAWStart - halfStep 1 = hexUnit 4 := by
            unfold hexAWStart halfStep
            rw [show (4 : ℤ) = 1 + 3 by norm_num,
              hexUnit_add_three]
            ring
          have hhead : hexInfra_headAccum 1 (base ++ [t]) =
              hexInfra_headAccum 1 base + t := by
            simp [hexInfra_headAccum_eq_add_sum, List.sum_append]
            ring
          rw [hhead] at hsame
          linear_combination hendMid - hsame + hstart
        obtain ⟨e, hbaseMid⟩ := hexEndpoint_mid_incident_aw base
          hexCSOutsideStartCoord happ.1.1 hlast
        have hpass : PassesThrough hexAWStart 1 (base ++ [t])
            (hexInfra_midAccum hexAWStart 1 base) := by
          have hp := hexEndpoint_prefix_mid_mem hexAWStart 1
            (base ++ [t]) base.length (by simp)
          simpa using hp
        have hmem : hexAWMid hexCSOutsideStartCoord e ∈ hexCSMids T L := by
          have := hadm.2.1 _ hpass
          change hexInfra_midAccum hexAWStart 1 base ∈ hexCSMids T L at this
          simpa [hbaseMid] using this
        have he : e = 0 :=
          (hexCSOutsideStart_mid_mem_iff T L hT e).mp hmem
        have hbaseEnd : (ofTurns hexAWStart 1 base).EndsAt hexAWStart := by
          unfold HexWalk.EndsAt
          rw [hexInfra_endMid_eq_midAccum, hbaseMid, he,
            hexCSOutsideStart_mid_zero]
        have hnil := hexReturningLegalSAW_eq_nil hexAWStart 1 base
          happ.1 hbaseEnd
        subst base
        have hzero : hexAWStart + halfStep 1 = 0 := by
          unfold hexAWStart halfStep
          rw [show (4 : ℤ) = 1 + 3 by norm_num,
            hexUnit_add_three]
          ring
        rw [hexInfra_midAccum_nil, hexInfra_headAccum_nil, hzero,
          hexCSOutsideStart_pos] at hlast
        exact hexUnit_ne_zero 4 hlast.symm
      · have hlast : hexInfra_midAccum hexAWStart 1 base +
            halfStep (hexInfra_headAccum 1 base) =
          hexAWStart + halfStep 1 := by
          rw [hexCyclic_midAccum_append_single] at hendMid
          have hhead : hexInfra_headAccum 1 (base ++ [t]) =
              hexInfra_headAccum 1 base + t := by
            simp [hexInfra_headAccum_eq_add_sum, List.sum_append]
            ring
          rw [hhead] at hopp
          linear_combination hendMid - hopp
        have hnil := hexReturn_eq_nil_of_lastVertex_eq_first
          hexAWStart 1 base happ.1.2 hlast
        subst base
        have heq : halfStep (1 + t) = halfStep (1 + 3) := by
          simpa [hexInfra_headAccum_nil] using
            hopp.trans (hexEndpoint_halfStep_add_three 1).symm
        have hdiv : (6 : ℤ) ∣ (1 + t) - (1 + 3) :=
          (hexUnit_eq_iff_mod _ _).mp (hexInfra_halfStep_inj heq)
        rcases ht with rfl | rfl <;> norm_num at hdiv

end

end StatMech.Universality

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Universality.HexCorrectedStripIdentity

namespace StatMech.Universality

open Complex HexWalk

noncomputable section



theorem hexCSOutsideBoundary_neighbor_not_mem
    {T L : ℕ} (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L) (f : Fin 3)
    (hf : f ≠ e.edge) :
    hexAWNeighbor (hexAWNeighbor e.vtx.1 e.edge) f ∉
      hexCSVertexSet T L := by
  rw [hexCS_mem_vertexSet_iff]
  have hc := (hexCS_mem_vertexSet_iff T L e.vtx.1).1 e.vtx.2
  have hb := hexCS_boundary_classification e he
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  cases color <;> fin_cases edge <;> fin_cases f <;>
    simp [hexAWNeighbor, hexCSInStrip, hexAWBookRe2, hexAWDepth,
      hexAWLong] at hc hb hf ⊢ <;> omega



theorem hexCSOutsideBoundary_not_mem
    {T L : ℕ} (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L) :
    hexAWNeighbor e.vtx.1 e.edge ∉ hexCSVertexSet T L := by
  rw [hexCS_mem_boundary_iff] at he
  exact he



theorem hexCSOutsideBoundary_mid_mem_iff
    {T L : ℕ} (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L) (f : Fin 3) :
    hexAWMid (hexAWNeighbor e.vtx.1 e.edge) f ∈ hexCSMids T L ↔
      f = e.edge := by
  constructor
  · intro hm
    by_contra hf
    rw [hexCSMids, Finset.mem_biUnion] at hm
    obtain ⟨v, _, hv⟩ := hm
    rw [Finset.mem_image] at hv
    obtain ⟨g, _, hg⟩ := hv
    have hedge := (hexAWMid_eq_iff
      (hexAWNeighbor e.vtx.1 e.edge) v.1 f g).mp hg.symm
    rcases hedge with ⟨hcoord, _⟩ | ⟨hcoord, _⟩
    · exact hexCSOutsideBoundary_not_mem e he (hcoord ▸ v.2)
    · exact hexCSOutsideBoundary_neighbor_not_mem e he f hf
        (hcoord ▸ v.2)
  · rintro rfl
    rw [hexAWMid_neighbor]
    rw [hexCSMids, Finset.mem_biUnion]
    refine ⟨e.vtx, Finset.mem_univ _, ?_⟩
    rw [Finset.mem_image]
    exact ⟨e.edge, Finset.mem_univ _, rfl⟩

theorem hexCSBoundaryIncidence_eq_start_of_mid
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (hmid : hexAWMid e.vtx.1 e.edge = hexAWStart) :
    e = hexCSStartIncidence T L hT := by
  have hm : hexAWMid hexAWOriginCoord 0 =
      hexAWMid e.vtx.1 e.edge := by
    rw [hexAWMid_origin_zero, hmid]
  rcases (hexAWMid_eq_iff hexAWOriginCoord e.vtx.1 0 e.edge).mp hm with
    ⟨hcoord, hedge⟩ | ⟨hcoord, hedge⟩
  · rw [HexIncidence.mk.injEq]
    exact ⟨Subtype.ext hcoord, hedge⟩
  · exfalso
    have hmem := e.vtx.2
    rw [hcoord, hexCS_mem_vertexSet_iff] at hmem
    simp [hexAWOriginCoord, hexAWNeighbor, hexCSInStrip,
      hexAWBookRe2, hexAWDepth, hexAWLong] at hmem

theorem hexCSCanonicalHeading_halfStep
    {T L : ℕ} (e : HexCSIncidence T L) :
    halfStep (hexCSCanonicalHeading e) =
      halfStep (hexAWHeading e.vtx.1 e.edge) := by
  unfold halfStep
  rw [hexCSCanonicalHeading_unit]



theorem hexCS_endpoint_boundary_exit
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    hexInfra_midAccum hexAWStart 1 ts +
        halfStep (hexInfra_headAccum 1 ts) =
      hexAWMid e.vtx.1 e.edge +
        halfStep (hexCSCanonicalHeading e) := by
  have hmid : hexInfra_midAccum hexAWStart 1 ts =
      hexAWMid e.vtx.1 e.edge := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact hadm.2.2
  have hforward := hexEndpoint_forward_vertex_of_mid ts e.vtx.1 e.edge
    hadm.1.1 hmid
  rcases hforward with hinside | houtside
  · induction ts using List.reverseRecOn with
    | nil =>
        exfalso
        apply hne
        apply hexCSBoundaryIncidence_eq_start_of_mid e
        simpa using hmid.symm
    | append_singleton s t ih =>
        have happ :=
          (endpointIsLegalSAW_append_one_iff hexAWStart 1 s t).mp hadm.1
        have hmidOuter :
            hexInfra_midAccum hexAWStart 1 (s ++ [t]) =
              hexAWMid (hexAWNeighbor e.vtx.1 e.edge) e.edge := by
          simpa using hmid
        have hforwardOuter :
            hexInfra_midAccum hexAWStart 1 (s ++ [t]) +
                halfStep (hexInfra_headAccum 1 (s ++ [t])) =
              hexAWPos (hexAWNeighbor
                (hexAWNeighbor e.vtx.1 e.edge) e.edge) := by
          simpa using hinside
        obtain ⟨f, hf, hprev⟩ :=
          hexEndpoint_previous_mid_of_forward_outer s t
            (hexAWNeighbor e.vtx.1 e.edge) e.edge
            happ.1.1 happ.2 hmidOuter hforwardOuter
        have hp := hexEndpoint_prefix_mid_mem hexAWStart 1 (s ++ [t])
          s.length (by simp)
        have hp' : PassesThrough hexAWStart 1 (s ++ [t])
            (hexInfra_midAccum hexAWStart 1 s) := by
          simpa using hp
        have hregion := hadm.2.1 _ hp'
        have hmem :
            hexAWMid (hexAWNeighbor e.vtx.1 e.edge) f ∈
              hexCSMids T L := by
          change hexInfra_midAccum hexAWStart 1 s ∈ hexCSMids T L at hregion
          rwa [hprev] at hregion
        exact (hf ((hexCSOutsideBoundary_mid_mem_iff e he f).mp hmem)).elim
  · calc
      hexInfra_midAccum hexAWStart 1 ts +
          halfStep (hexInfra_headAccum 1 ts) =
          hexAWPos (hexAWNeighbor e.vtx.1 e.edge) := houtside
      _ = hexAWMid e.vtx.1 e.edge +
          halfStep (hexAWHeading e.vtx.1 e.edge) :=
        hexAWNeighborPos_eq_mid_add e.vtx.1 e.edge
      _ = hexAWMid e.vtx.1 e.edge +
          halfStep (hexCSCanonicalHeading e) := by
        rw [hexCSCanonicalHeading_halfStep]

theorem hexCS_boundaryExitLaw (T L : ℕ) (hT : 0 < T) :
    HexCSBoundaryExitLaw T L hT := by
  intro e ts he hne hadm
  exact hexCS_endpoint_boundary_exit e ts he hne hadm

end

end StatMech.Universality

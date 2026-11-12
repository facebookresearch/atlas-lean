/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Universality.HexCorrectedStripLimits
import Code.Universality.HexEndpointVertex

namespace StatMech.Universality

open HexWalk

noncomputable section



theorem hexEndpoint_unit_depthStep_le_three
    (d : HexReturnCoord) (hd : d.IsUnit) :
    2 * d.x - d.y ≤ 3 := by
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num



theorem hexEndpointCoordRun_depth_le
    (p d : HexReturnCoord) (ts : List ℤ)
    (hd : d.IsUnit) (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    let r := hexEndpointCoordRun p d ts
    2 * r.pos.x - r.pos.y ≤
      2 * p.x - p.y + 3 * (ts.length : ℤ) := by
  induction ts generalizing p d with
  | nil => simp [hexEndpointCoordRun]
  | cons t ts ih =>
      have ht := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      let e := d.turn t
      have he : e.IsUnit := HexReturnCoord.isUnit_turn hd ht
      have hstep := hexEndpoint_unit_depthStep_le_three e he
      have hrec := ih (p.add e) e he htail
      change 2 * (hexEndpointCoordRun (p.add e) e ts).pos.x -
          (hexEndpointCoordRun (p.add e) e ts).pos.y ≤
        2 * p.x - p.y + 3 * ((t :: ts).length : ℤ)
      calc
        2 * (hexEndpointCoordRun (p.add e) e ts).pos.x -
              (hexEndpointCoordRun (p.add e) e ts).pos.y ≤
            2 * (p.add e).x - (p.add e).y +
              3 * (ts.length : ℤ) := hrec
        _ ≤ 2 * p.x - p.y + 3 + 3 * (ts.length : ℤ) := by
          simp only [HexReturnCoord.add]
          omega
        _ = 2 * p.x - p.y + 3 * ((t :: ts).length : ℤ) := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring


theorem hexEndpointCoordRun_depth_le_length
    (ts : List ℤ) (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    let r := hexEndpointCoordRun HexReturnCoord.zero
      HexReturnCoord.base ts
    2 * r.pos.x - r.pos.y ≤ 3 * (ts.length : ℤ) := by
  have h := hexEndpointCoordRun_depth_le HexReturnCoord.zero
    HexReturnCoord.base ts HexReturnCoord.base_isUnit hlegal
  simpa [HexReturnCoord.zero] using h




theorem hexAW_three_depth_sub_two_le_returnPos (c : HexAWCoord) :
    3 * hexAWDepth c - 2 ≤
      2 * (hexAWReturnPos c).x - (hexAWReturnPos c).y := by
  rcases c with ⟨i, j, color⟩
  cases color <;>
    simp [hexAWDepth, hexAWLong, hexAWReturnPos] <;> omega

@[simp] theorem hexAWDepth_neighbor_zero (c : HexAWCoord) :
    hexAWDepth (hexAWNeighbor c 0) = hexAWDepth c := by
  rcases c with ⟨i, j, color⟩
  cases color <;> simp [hexAWNeighbor, hexAWDepth, hexAWLong]





theorem hexEndpoint_length_ge_of_endsAt_depth
    (T : ℕ) (ts : List ℤ) (c : HexAWCoord)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (hdepth : hexAWDepth c = T)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c 0)) :
    T ≤ ts.length := by
  have hturns : ∀ t ∈ ts, t = 1 ∨ t = -1 := hlegal.1
  have hrun := hexEndpointCoordRun_depth_le_length ts hturns
  have hmid : hexInfra_midAccum hexAWStart 1 ts = hexAWMid c 0 := by
    unfold EndsAt at hend
    rw [hexInfra_endMid_eq_midAccum] at hend
    exact hend
  have hforward := hexEndpoint_forward_vertex_of_mid ts c 0 hturns hmid
  have finish (d : HexAWCoord)
      (hd : hexAWDepth d = T)
      (hvertex : hexInfra_midAccum hexAWStart 1 ts +
        halfStep (hexInfra_headAccum 1 ts) = hexAWPos d) : T ≤ ts.length := by
    have hpos := hexEndpointCoordRun_pos_eq_aw ts d hturns hvertex
    change 2 * (hexEndpointCoordRun HexReturnCoord.zero
      HexReturnCoord.base ts).pos.x -
        (hexEndpointCoordRun HexReturnCoord.zero
          HexReturnCoord.base ts).pos.y ≤ 3 * (ts.length : ℤ) at hrun
    rw [hpos] at hrun
    have hlower := hexAW_three_depth_sub_two_le_returnPos d
    rw [hd] at hlower
    have hcast : (T : ℤ) ≤ (ts.length : ℤ) := by omega
    exact_mod_cast hcast
  rcases hforward with hforward | hforward
  · exact finish c hdepth hforward
  · exact finish (hexAWNeighbor c 0)
      (by simpa [hdepth]) hforward



theorem hexCSTopWalk_length_ge
    (T L : ℕ) (hT : 0 < T) (ts : List ℤ)
    (hwalk : HexCSTopWalk T L hT ts) :
    T ≤ (ofTurns hexAWStart 1 ts).endpointNumVertices := by
  obtain ⟨hlegal, _, c, _, _, hdepth, hend⟩ := hwalk
  simpa [endpointNumVertices] using
    hexEndpoint_length_ge_of_endsAt_depth T ts c hlegal hdepth hend


theorem hexCSTopWalkAtWidth_length_ge
    (T : ℕ) (hT : 0 < T) (ts : List ℤ)
    (hwalk : HexCSTopWalkAtWidth T hT ts) :
    T ≤ (ofTurns hexAWStart 1 ts).endpointNumVertices := by
  obtain ⟨L, hL⟩ := hwalk
  exact hexCSTopWalk_length_ge T L hT ts hL

end

end StatMech.Universality

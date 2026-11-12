/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Universality.HexLiteralHWColumns
import Code.Universality.HexEndpointLocalGeometry

namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhc_prefixCoord_eq_endpointPrefixCoord (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) (k : ℕ) :
    hlhc_prefixCoord ts hleg.1 k =
      hexEndpointPrefixCoord ts hleg.1 k := by
  unfold hlhc_prefixCoord hexEndpointPrefixCoord
  congr

theorem hlhc_prefixCoord_adjacent (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (k : ℕ) (hk : k < ts.length) :
    ∃ e : Fin 3,
      hexAWNeighbor (hlhc_prefixCoord ts hleg.1 k) e =
        hlhc_prefixCoord ts hleg.1 (k + 1) := by
  simpa only [hlhc_prefixCoord_eq_endpointPrefixCoord] using
    hexEndpointPrefixCoord_adjacent ts hleg.1 k hk

theorem hlhc_prefixCoord_adjacent_legal (ts : List ℤ)
    (hlegal : (ofTurns hexAWStart 1 ts).LegalTurns)
    (k : ℕ) (hk : k < ts.length) :
    ∃ e : Fin 3,
      hexAWNeighbor (hlhc_prefixCoord ts hlegal k) e =
        hlhc_prefixCoord ts hlegal (k + 1) := by
  have hcoord (r : ℕ) :
      hlhc_prefixCoord ts hlegal r =
        hexEndpointPrefixCoord ts hlegal r := by
    unfold hlhc_prefixCoord hexEndpointPrefixCoord
    congr
  simpa only [hcoord] using
    hexEndpointPrefixCoord_adjacent ts hlegal k hk



theorem hlhd_prefix_edge_unit (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (k : ℕ) (hk : k < ts.length) (e : Fin 3)
    (he : hexAWNeighbor (hlhc_prefixCoord ts hleg.1 k) e =
      hlhc_prefixCoord ts hleg.1 (k + 1)) :
    hexUnit (hexInfra_headAccum 1 (ts.take (k + 1))) =
      hexUnit (hexAWHeading (hlhc_prefixCoord ts hleg.1 k) e) := by
  have hstep :
      hexJordan_vertexPos hexAWStart 1 ts (k + 1) -
          hexJordan_vertexPos hexAWStart 1 ts k =
        hexUnit (hexInfra_headAccum 1 (ts.take (k + 1))) := by
    rw [hexEndpoint_vertexPos_eq_nextMid_sub ts k hk]
    unfold hexJordan_vertexPos
    unfold halfStep
    ring
  have hkpos : hexJordan_vertexPos hexAWStart 1 ts k =
      hexAWPos (hlhc_prefixCoord ts hleg.1 k) := by
    simpa only [hexJordan_vertexPos] using
      hlhc_prefixCoord_vertex ts hleg.1 k
  have hsuccpos : hexJordan_vertexPos hexAWStart 1 ts (k + 1) =
      hexAWPos (hlhc_prefixCoord ts hleg.1 (k + 1)) := by
    simpa only [hexJordan_vertexPos] using
      hlhc_prefixCoord_vertex ts hleg.1 (k + 1)
  rw [hkpos, hsuccpos] at hstep
  have hcoord :
      hexAWPos (hlhc_prefixCoord ts hleg.1 (k + 1)) -
          hexAWPos (hlhc_prefixCoord ts hleg.1 k) =
        hexUnit (hexAWHeading (hlhc_prefixCoord ts hleg.1 k) e) := by
    rw [← he]
    exact hexAWPos_neighbor _ _
  exact hstep.symm.trans hcoord



theorem hlhd_midAccum_prefixEdge (ts : List ℤ)
    (hlegal : (ofTurns hexAWStart 1 ts).LegalTurns)
    (k : ℕ) (hkpos : 0 < k) (hkle : k ≤ ts.length)
    (e : Fin 3)
    (he : hexAWNeighbor (hlhc_prefixCoord ts hlegal (k - 1)) e =
      hlhc_prefixCoord ts hlegal k) :
    hexInfra_midAccum hexAWStart 1 (ts.take k) =
      hexAWMid (hlhc_prefixCoord ts hlegal (k - 1)) e := by
  have hk : k - 1 < ts.length := by omega
  have hprev := hexEndpoint_vertexPos_eq_nextMid_sub ts (k - 1) hk
  have hprevPos := hlhc_prefixCoord_vertex ts hlegal (k - 1)
  have hfinalPos := hlhc_prefixCoord_vertex ts hlegal k
  have hsubadd : k - 1 + 1 = k := by omega
  rw [hsubadd] at hprev
  unfold hexJordan_vertexPos at hprev
  unfold hexAWMid
  rw [he]
  rw [← hprevPos, ← hfinalPos]
  rw [hprev]
  ring



theorem hlhc_prefixCoord_append_single (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) (t : ℤ)
    (hleg' : (ofTurns hexAWStart 1 (ts ++ [t])).IsLegalSAW)
    (k : ℕ) (hk : k ≤ ts.length) :
    hlhc_prefixCoord (ts ++ [t]) hleg'.1 k =
      hlhc_prefixCoord ts hleg.1 k := by
  apply hexAWPos_injective
  rw [← hlhc_prefixCoord_vertex (ts ++ [t]) hleg'.1 k,
    ← hlhc_prefixCoord_vertex ts hleg.1 k,
    List.take_append_of_le_length hk]

theorem hlhd_neighbor_depth_cases (c : HexAWCoord) (e : Fin 3) :
    (hexAWDepth (hexAWNeighbor c e) = hexAWDepth c + 1 ∧
        c.color = .black ∧ (e = 1 ∨ e = 2)) ∨
      (hexAWDepth (hexAWNeighbor c e) = hexAWDepth c - 1 ∧
        c.color = .white ∧ (e = 1 ∨ e = 2)) ∨
      (hexAWDepth (hexAWNeighbor c e) = hexAWDepth c ∧ e = 0) := by
  rcases c with ⟨i, j, color⟩
  cases color <;> fin_cases e <;>
    simp [hexAWNeighbor, hexAWDepth, hexAWLong] <;> omega



noncomputable def hlhd_depth (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) (k : ℕ) : ℤ :=
  hexAWDepth (hlhc_prefixCoord ts hleg.1 k)


noncomputable def hlhd_height (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) (k : ℕ) : ℝ :=
  hlhd_depth ts hleg k


def HLHDLiteralHalfSpace (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) : Prop :=
  ∀ k, 0 < k → k ≤ ts.length →
    hlhd_height ts hleg 0 < hlhd_height ts hleg k

theorem hlhd_halfSpace_ahead (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg) :
    HLHRAhead (hlhd_height ts hleg) true 0 ts.length := by
  intro k hk hklen
  simpa [hlhr_signed] using hhalf k hk hklen


noncomputable def hlhd_intervals (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    List (ℕ × ℕ) :=
  hlhr_intervalsAux (hlhd_height ts hleg) ts.length ts.length true 0


def hlhd_intervalTurns (ts : List ℤ) (ps : List (ℕ × ℕ)) : List ℤ :=
  hlhr_intervalTurns ts ps

theorem hlhd_intervals_reconstruct (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg) :
    hlhd_intervalTurns ts (hlhd_intervals ts hleg) = ts := by
  by_cases hempty : ts = []
  · simp [hempty, hlhd_intervalTurns, hlhd_intervals,
      hlhr_intervalsAux, hlhr_intervalTurns]
  · apply hlhr_intervalsAux_reconstruct (hlhd_height ts hleg) ts
      ts.length 0 true (by omega) (by omega)
    intro _
    exact hlhd_halfSpace_ahead ts hleg hhalf






def HLHRBridgeInterval (f : ℕ → ℝ) (up : Bool)
    (p : ℕ × ℕ) : Prop :=
  p.1 < p.2 ∧
    (∀ j, p.1 < j → j ≤ p.2 →
      hlhr_signed up (f p.1) < hlhr_signed up (f j)) ∧
    ∀ j, p.1 ≤ j → j ≤ p.2 →
      hlhr_signed up (f j) ≤ hlhr_signed up (f p.2)

theorem hlhr_intervalsAux_bridge (f : ℕ → ℝ) (hi fuel lo : ℕ)
    (up : Bool) (hlt : lo < hi) (hahead : HLHRAhead f up lo hi) :
    ∀ p ∈ hlhr_intervalsAux f hi fuel up lo,
      ∃ dir, HLHRBridgeInterval f dir p := by
  induction fuel generalizing lo up with
  | zero => simp [hlhr_intervalsAux]
  | succ fuel ih =>
      let k := hlhr_lastExtremum f up lo hi
      have hklo : lo < k := by
        dsimp [k]
        exact hlhr_lastExtremum_gt f up hlt hahead
      have hkhi : k ≤ hi := by
        dsimp [k]
        exact hlhr_lastExtremum_le_hi f up (le_of_lt hlt)
      intro p hp
      simp only [hlhr_intervalsAux, hlt, ↓reduceIte, List.mem_cons] at hp
      rcases hp with rfl | hp
      · refine ⟨up, hklo, ?_, ?_⟩
        · intro j hjlo hjhi
          exact hahead j hjlo (le_trans hjhi hkhi)
        · intro j hjlo hjhi
          exact (hlhr_lastExtremum_spec f up (le_of_lt hlt)).2.2
            j hjlo (le_trans hjhi hkhi)
      · by_cases hk : k < hi
        · exact ih k (!up) hk (hlhr_ahead_next f up hlt) p hp
        · have hkeq : k = hi := by omega
          have htail : hlhr_intervalsAux f hi fuel (!up) k = [] := by
            rw [hkeq]
            cases fuel <;> simp [hlhr_intervalsAux]
          rw [htail] at hp
          simp at hp

theorem hlhd_interval_is_bridge (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    ∃ up, HLHRBridgeInterval (hlhd_height ts hleg) up p := by
  have hne : ts ≠ [] := by
    intro hempty
    simp [hlhd_intervals, hempty, hlhr_intervalsAux] at hp
  exact hlhr_intervalsAux_bridge (hlhd_height ts hleg) ts.length
    ts.length 0 true (List.length_pos_iff.mpr hne)
      (hlhd_halfSpace_ahead ts hleg hhalf) p hp




theorem hlhd_bridge_source_color (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (p : ℕ × ℕ) (hp2 : p.2 ≤ ts.length)
    {up : Bool} (hb : HLHRBridgeInterval (hlhd_height ts hleg) up p) :
    (up = true ∧
        (hlhc_prefixCoord ts hleg.1 p.1).color = .black) ∨
      (up = false ∧
        (hlhc_prefixCoord ts hleg.1 p.1).color = .white) := by
  have hk : p.1 < ts.length := lt_of_lt_of_le hb.1 hp2
  obtain ⟨e, he⟩ := hlhc_prefixCoord_adjacent ts hleg p.1 hk
  have hstep := hb.2.1 (p.1 + 1) (Nat.lt_succ_self p.1)
    (Nat.succ_le_iff.mpr hb.1)
  have hcases := hlhd_neighbor_depth_cases
    (hlhc_prefixCoord ts hleg.1 p.1) e
  cases up with
  | false =>
      right
      refine ⟨rfl, ?_⟩
      simp only [hlhr_signed, Bool.false_eq_true, ↓reduceIte,
        hlhd_height, hlhd_depth] at hstep
      rw [← he] at hstep
      rcases hcases with hinc | hdec | hflat
      · rw [hinc.1] at hstep
        push_cast at hstep
        norm_num at hstep
      · exact hdec.2.1
      · rw [hflat.1] at hstep
        exact (lt_irrefl _ hstep).elim
  | true =>
      left
      refine ⟨rfl, ?_⟩
      simp only [hlhr_signed, ↓reduceIte, hlhd_height, hlhd_depth] at hstep
      rw [← he] at hstep
      rcases hcases with hinc | hdec | hflat
      · exact hinc.2.1
      · rw [hdec.1] at hstep
        push_cast at hstep
        linarith
      · rw [hflat.1] at hstep
        exact (lt_irrefl _ hstep).elim


theorem hlhd_bridge_depth_bounds (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (p : ℕ × ℕ) {up : Bool}
    (hb : HLHRBridgeInterval (hlhd_height ts hleg) up p)
    {k : ℕ} (hklo : p.1 ≤ k) (hkhi : k ≤ p.2) :
    hlhr_signed up (hlhd_height ts hleg p.1) ≤
        hlhr_signed up (hlhd_height ts hleg k) ∧
      hlhr_signed up (hlhd_height ts hleg k) ≤
        hlhr_signed up (hlhd_height ts hleg p.2) := by
  constructor
  · rcases eq_or_lt_of_le hklo with rfl | hk
    · exact le_rfl
    · exact le_of_lt (hb.2.1 k hk hkhi)
  · exact hb.2.2 k hklo hkhi



theorem hlhd_interval_index_bounds (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg) :
    ∀ p ∈ hlhd_intervals ts hleg, p.1 < p.2 ∧ p.2 ≤ ts.length := by
  intro p hp
  have hne : ts ≠ [] := by
    intro hempty
    simp [hlhd_intervals, hempty, hlhr_intervalsAux] at hp
  exact hlhr_intervalsAux_bounds (hlhd_height ts hleg) ts.length
    ts.length 0 true (List.length_pos_iff.mpr hne)
      (hlhd_halfSpace_ahead ts hleg hhalf) p hp |>.2


noncomputable def hlhd_intervalUp (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) : Bool :=
  Classical.choose (hlhd_interval_is_bridge ts hleg hhalf p hp)

theorem hlhd_intervalUp_bridge (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    HLHRBridgeInterval (hlhd_height ts hleg)
      (hlhd_intervalUp ts hleg hhalf p hp) p :=
  Classical.choose_spec (hlhd_interval_is_bridge ts hleg hhalf p hp)

noncomputable def hlhd_intervalFirstEdge (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) : Fin 3 := by
  have hb := hlhd_interval_index_bounds ts hleg hhalf p hp
  exact Classical.choose (hlhc_prefixCoord_adjacent ts hleg p.1
    (lt_of_lt_of_le hb.1 hb.2))

theorem hlhd_intervalFirstEdge_spec (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hexAWNeighbor (hlhc_prefixCoord ts hleg.1 p.1)
        (hlhd_intervalFirstEdge ts hleg hhalf p hp) =
      hlhc_prefixCoord ts hleg.1 (p.1 + 1) := by
  unfold hlhd_intervalFirstEdge
  exact Classical.choose_spec (hlhc_prefixCoord_adjacent ts hleg p.1
    (lt_of_lt_of_le (hlhd_interval_index_bounds ts hleg hhalf p hp).1
      (hlhd_interval_index_bounds ts hleg hhalf p hp).2))

theorem hlhd_intervalLastEdge_exists (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    ∃ e : Fin 3,
      hexAWNeighbor (hlhc_prefixCoord ts hleg.1 (p.2 - 1)) e =
        hlhc_prefixCoord ts hleg.1 p.2 := by
  have hb := hlhd_interval_index_bounds ts hleg hhalf p hp
  obtain ⟨e, he⟩ := hlhc_prefixCoord_adjacent ts hleg (p.2 - 1)
    (by omega)
  refine ⟨e, ?_⟩
  have hp2pos : 0 < p.2 := lt_of_le_of_lt (Nat.zero_le p.1) hb.1
  have hp2one : 1 ≤ p.2 := hp2pos
  simpa only [Nat.sub_add_cancel hp2one] using he

noncomputable def hlhd_intervalLastEdge (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) : Fin 3 :=
  Classical.choose (hlhd_intervalLastEdge_exists ts hleg hhalf p hp)

theorem hlhd_intervalLastEdge_spec (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hexAWNeighbor (hlhc_prefixCoord ts hleg.1 (p.2 - 1))
        (hlhd_intervalLastEdge ts hleg hhalf p hp) =
      hlhc_prefixCoord ts hleg.1 p.2 := by
  unfold hlhd_intervalLastEdge
  exact Classical.choose_spec
    (hlhd_intervalLastEdge_exists ts hleg hhalf p hp)

theorem hlhd_bridge_first_edge_inward (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (p : ℕ × ℕ) {up : Bool}
    (hb : HLHRBridgeInterval (hlhd_height ts hleg) up p)
    (hp2 : p.2 ≤ ts.length) (e : Fin 3)
    (he : hexAWNeighbor (hlhc_prefixCoord ts hleg.1 p.1) e =
      hlhc_prefixCoord ts hleg.1 (p.1 + 1)) :
    e = 1 ∨ e = 2 := by
  have hk : p.1 < ts.length := lt_of_lt_of_le hb.1 hp2
  have hstep := hb.2.1 (p.1 + 1) (Nat.lt_succ_self p.1)
    (Nat.succ_le_iff.mpr hb.1)
  simp only [hlhd_height, hlhd_depth] at hstep
  rw [← he] at hstep
  rcases hlhd_neighbor_depth_cases
      (hlhc_prefixCoord ts hleg.1 p.1) e with hinc | hdec | hflat
  · exact hinc.2.2
  · exact hdec.2.2
  · rw [hflat.1] at hstep
    cases up <;> simp [hlhr_signed] at hstep

theorem hlhd_intervalFirstEdge_inward (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hlhd_intervalFirstEdge ts hleg hhalf p hp = 1 ∨
      hlhd_intervalFirstEdge ts hleg hhalf p hp = 2 := by
  exact hlhd_bridge_first_edge_inward ts hleg p
    (hlhd_intervalUp_bridge ts hleg hhalf p hp)
    (hlhd_interval_index_bounds ts hleg hhalf p hp).2 _
    (hlhd_intervalFirstEdge_spec ts hleg hhalf p hp)



def hlhd_swapColor : HexAWColor → HexAWColor
  | .black => .white
  | .white => .black

@[simp] theorem hlhd_swapColor_invol (c : HexAWColor) :
    hlhd_swapColor (hlhd_swapColor c) = c := by
  cases c <;> rfl




def hlhd_normalizeCoord (up : Bool) (source c : HexAWCoord) : HexAWCoord :=
  if up then
    ⟨c.i - source.i, c.j - source.j, c.color⟩
  else
    ⟨source.i - c.i, source.j - c.j, hlhd_swapColor c.color⟩

theorem hlhd_normalizeCoord_depth (up : Bool) (source c : HexAWCoord) :
    hexAWDepth (hlhd_normalizeCoord up source c) =
      if up then hexAWDepth c - hexAWDepth source
      else hexAWDepth source - hexAWDepth c := by
  rcases source with ⟨si, sj, sc⟩
  rcases c with ⟨i, j, color⟩
  cases up <;> simp [hlhd_normalizeCoord, hexAWDepth, hexAWLong] <;> omega

theorem hlhd_normalizeCoord_neighbor (up : Bool) (source c : HexAWCoord)
    (e : Fin 3) :
    hlhd_normalizeCoord up source (hexAWNeighbor c e) =
      hexAWNeighbor (hlhd_normalizeCoord up source c) e := by
  rcases source with ⟨si, sj, sc⟩
  rcases c with ⟨i, j, color⟩
  cases up <;> cases color <;> fin_cases e <;>
    simp [hlhd_normalizeCoord, hlhd_swapColor, hexAWNeighbor] <;> omega

theorem hlhd_normalizeCoord_source_up (source : HexAWCoord)
    (hc : source.color = .black) :
    hlhd_normalizeCoord true source source = hexAWOriginCoord := by
  rcases source with ⟨i, j, color⟩
  cases color <;> simp_all [hlhd_normalizeCoord, hlhd_swapColor,
    hexAWOriginCoord]

theorem hlhd_normalizeCoord_source_down (source : HexAWCoord)
    (hc : source.color = .white) :
    hlhd_normalizeCoord false source source = hexAWOriginCoord := by
  rcases source with ⟨i, j, color⟩
  cases color <;> simp_all [hlhd_normalizeCoord, hlhd_swapColor,
    hexAWOriginCoord]

theorem hlhd_normalizeCoord_heading (up : Bool) (source c : HexAWCoord)
    (e : Fin 3) :
    hexAWHeading (hlhd_normalizeCoord up source c) e =
      if up then hexAWHeading c e
      else match c.color with
        | .black => hexAWHeading c e + 3
        | .white => hexAWHeading c e - 3 := by
  rcases source with ⟨si, sj, sc⟩
  rcases c with ⟨i, j, color⟩
  cases up <;> cases color <;> fin_cases e <;>
    simp [hlhd_normalizeCoord, hlhd_swapColor, hexAWHeading]

theorem hlhd_normalizeCoord_pos (up : Bool) (source c : HexAWCoord)
    (hsource : if up then source.color = .black else source.color = .white) :
    hexAWPos (hlhd_normalizeCoord up source c) =
      if up then hexAWPos c - hexAWPos source
      else hexAWPos source - hexAWPos c := by
  rcases source with ⟨si, sj, sc⟩
  rcases c with ⟨i, j, color⟩
  cases up <;> cases sc <;> cases color <;>
    simp_all [hlhd_normalizeCoord, hlhd_swapColor, hexAWPos] <;> ring



def hlhd_normalizeHeading (up : Bool) (h : Fin 6) : Fin 6 :=
  if up then h else h + 3



def hlhd_edgeOfHeading (c : HexAWCoord) (h : Fin 6) : Fin 3 :=
  match c.color, h.val with
  | .black, 4 => 0
  | .black, 0 => 1
  | .black, 2 => 2
  | .white, 1 => 0
  | .white, 3 => 1
  | .white, 5 => 2
  | _, _ => 0



def hlhd_coordPath : HexAWCoord → Fin 6 → List ℤ → List HexAWCoord
  | c, h, [] => [c, hexAWNeighbor c (hlhd_edgeOfHeading c h)]
  | c, h, t :: ts =>
      c :: hlhd_coordPath
        (hexAWNeighbor c (hlhd_edgeOfHeading c h))
        (hexHeadingTurn h t) ts

@[simp] theorem hlhd_normalizeHeading_true (h : Fin 6) :
    hlhd_normalizeHeading true h = h := rfl

@[simp] theorem hlhd_normalizeHeading_false (h : Fin 6) :
    hlhd_normalizeHeading false h = h + 3 := rfl

theorem hlhd_edgeOfHeading_normalize (up : Bool) (source c : HexAWCoord)
    (h : Fin 6) :
    hlhd_edgeOfHeading (hlhd_normalizeCoord up source c)
        (hlhd_normalizeHeading up h) =
      hlhd_edgeOfHeading c h := by
  rcases source with ⟨si, sj, sc⟩
  rcases c with ⟨i, j, color⟩
  cases up <;> cases color <;> fin_cases h <;>
    simp [hlhd_normalizeCoord, hlhd_normalizeHeading, hlhd_swapColor,
      hlhd_edgeOfHeading]

theorem hlhd_normalizeHeading_turn (up : Bool) (h : Fin 6) (t : ℤ)
    (ht : t = 1 ∨ t = -1) :
    hlhd_normalizeHeading up (hexHeadingTurn h t) =
      hexHeadingTurn (hlhd_normalizeHeading up h) t := by
  rcases ht with rfl | rfl <;> cases up <;> fin_cases h <;> decide



theorem hlhd_coordPath_normalize (up : Bool) (source c : HexAWCoord)
    (h : Fin 6) (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    (hlhd_coordPath c h ts).map (hlhd_normalizeCoord up source) =
      hlhd_coordPath (hlhd_normalizeCoord up source c)
        (hlhd_normalizeHeading up h) ts := by
  induction ts generalizing c h with
  | nil =>
      simp [hlhd_coordPath, hlhd_edgeOfHeading_normalize,
        hlhd_normalizeCoord_neighbor]
  | cons t ts ih =>
      have ht : t = 1 ∨ t = -1 := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      simp only [hlhd_coordPath, List.map_cons, List.cons.injEq, true_and]
      rw [ih _ _ htail, hlhd_normalizeCoord_neighbor,
        hlhd_edgeOfHeading_normalize,
        hlhd_normalizeHeading_turn up h t ht]

theorem hlhd_interval_source_normalizes (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hlhd_normalizeCoord (hlhd_intervalUp ts hleg hhalf p hp)
        (hlhc_prefixCoord ts hleg.1 p.1)
        (hlhc_prefixCoord ts hleg.1 p.1) = hexAWOriginCoord := by
  have hc := hlhd_bridge_source_color ts hleg p
    (hlhd_interval_index_bounds ts hleg hhalf p hp).2
    (hlhd_intervalUp_bridge ts hleg hhalf p hp)
  rcases hc with ⟨hup, hblack⟩ | ⟨hup, hwhite⟩
  · rw [hup]
    exact hlhd_normalizeCoord_source_up _ hblack
  · rw [hup]
    exact hlhd_normalizeCoord_source_down _ hwhite


def hlhd_entryTurn (e : Fin 3) : ℤ :=
  if e = 1 then -1 else 1

theorem hlhd_entryTurn_legal (e : Fin 3) :
    hlhd_entryTurn e = 1 ∨ hlhd_entryTurn e = -1 := by
  unfold hlhd_entryTurn
  split <;> simp

theorem hlhd_entryTurn_heading {e : Fin 3} (he : e = 1 ∨ e = 2) :
    1 + hlhd_entryTurn e = hexAWHeading hexAWOriginCoord e := by
  rcases he with rfl | rfl <;>
    simp [hlhd_entryTurn, hexAWHeading, hexAWOriginCoord]


def hlhd_exitTurn (e : Fin 3) : ℤ :=
  if e = 1 then 1 else -1

theorem hlhd_exitTurn_legal (e : Fin 3) :
    hlhd_exitTurn e = 1 ∨ hlhd_exitTurn e = -1 := by
  unfold hlhd_exitTurn
  split <;> simp

theorem hlhd_exitTurn_heading {e : Fin 3} (he : e = 1 ∨ e = 2) :
    hexAWHeading (HexAWCoord.mk 0 0 .black) e + hlhd_exitTurn e = 1 := by
  rcases he with rfl | rfl <;>
    simp [hlhd_exitTurn, hexAWHeading]





structure HLHDColumnTag where
  up : Bool
  firstPositive : Bool
  exits : Bool
  deriving DecidableEq, Fintype

@[simp] theorem hlhd_columnTag_card : Fintype.card HLHDColumnTag = 8 := by
  decide

def hlhd_turnBit (t : ℤ) : Bool := decide (t = 1)

def hlhd_bitTurn (b : Bool) : ℤ := if b then 1 else -1

theorem hlhd_bitTurn_turnBit {t : ℤ} (ht : t = 1 ∨ t = -1) :
    hlhd_bitTurn (hlhd_turnBit t) = t := by
  rcases ht with rfl | rfl <;>
    simp [hlhd_bitTurn, hlhd_turnBit]



def hlhd_coreTurns (entry : ℤ) (raw : List ℤ) : List ℤ :=
  entry :: raw.tail



def hlhd_endpointTurns (exits : Bool) (exitTurn : ℤ)
    (core : List ℤ) : List ℤ :=
  if exits then core ++ [exitTurn] else core


def hlhd_decodeColumn (tag : HLHDColumnTag) (out : List ℤ) : List ℤ :=
  hlhd_bitTurn tag.firstPositive ::
    (if tag.exits then out.dropLast else out).tail

theorem hlhd_endpointTurns_length (exits : Bool) (exitTurn : ℤ)
    (core : List ℤ) :
    (hlhd_endpointTurns exits exitTurn core).length = core.length ∨
      (hlhd_endpointTurns exits exitTurn core).length = core.length + 1 := by
  cases exits <;> simp [hlhd_endpointTurns]

theorem hlhd_coreTurns_length {raw : List ℤ} (hraw : raw ≠ [])
    (entry : ℤ) :
    (hlhd_coreTurns entry raw).length = raw.length := by
  cases raw with
  | nil => exact (hraw rfl).elim
  | cons t tail => simp [hlhd_coreTurns]

theorem hlhd_decodeColumn_encode {raw : List ℤ} (hraw : raw ≠ [])
    (hlegal : ∀ t ∈ raw, t = 1 ∨ t = -1)
    (up exits : Bool) (entry exitTurn : ℤ) :
    hlhd_decodeColumn
        ⟨up, hlhd_turnBit raw.head!, exits⟩
        (hlhd_endpointTurns exits exitTurn (hlhd_coreTurns entry raw)) = raw := by
  cases raw with
  | nil => exact (hraw rfl).elim
  | cons t tail =>
      have ht : t = 1 ∨ t = -1 := hlegal t (by simp)
      cases exits with
      | false =>
          simp [hlhd_decodeColumn, hlhd_endpointTurns, hlhd_coreTurns,
            hlhd_bitTurn_turnBit ht]
      | true =>
          simp only [hlhd_decodeColumn, hlhd_endpointTurns, ↓reduceIte,
            hlhd_coreTurns, List.tail_cons]
          rw [List.dropLast_append_of_ne_nil
            (by simp : [exitTurn] ≠ []), List.dropLast_singleton,
            List.append_nil, List.tail_cons]
          change hlhd_bitTurn (hlhd_turnBit t) :: tail = t :: tail
          rw [hlhd_bitTurn_turnBit ht]



theorem hlhd_raw_eq_of_tagged_eq
    {raw raw' : List ℤ} (hraw : raw ≠ []) (hraw' : raw' ≠ [])
    (hlegal : ∀ t ∈ raw, t = 1 ∨ t = -1)
    (hlegal' : ∀ t ∈ raw', t = 1 ∨ t = -1)
    {up up' exits exits' : Bool} {entry entry' exitTurn exitTurn' : ℤ}
    (htag : (HLHDColumnTag.mk up (hlhd_turnBit raw.head!) exits) =
      HLHDColumnTag.mk up' (hlhd_turnBit raw'.head!) exits')
    (hout : hlhd_endpointTurns exits exitTurn (hlhd_coreTurns entry raw) =
      hlhd_endpointTurns exits' exitTurn' (hlhd_coreTurns entry' raw')) :
    raw = raw' := by
  have hdecode :
      hlhd_decodeColumn
          ⟨up, hlhd_turnBit raw.head!, exits⟩
          (hlhd_endpointTurns exits exitTurn (hlhd_coreTurns entry raw)) =
        hlhd_decodeColumn
          ⟨up', hlhd_turnBit raw'.head!, exits'⟩
          (hlhd_endpointTurns exits' exitTurn'
            (hlhd_coreTurns entry' raw')) := by
    rw [htag, hout]
  rw [hlhd_decodeColumn_encode hraw hlegal up exits entry exitTurn,
    hlhd_decodeColumn_encode hraw' hlegal' up' exits' entry' exitTurn'] at hdecode
  exact hdecode





theorem hlhd_interval_legal (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    {p : ℕ × ℕ} (hp : p ∈ hlhd_intervals ts hleg) :
    (ofTurns (hlhr_pieceMid hexAWStart 1 ts p.1)
      (hlhr_pieceHead 1 ts p.1) (hlhr_intervalContent ts p)).IsLegalSAW := by
  have hne : ts ≠ [] := by
    intro hempty
    simp [hlhd_intervals, hempty, hlhr_intervalsAux] at hp
  have hb := hlhr_intervalsAux_bounds (hlhd_height ts hleg) ts.length
    ts.length 0 true (List.length_pos_iff.mpr hne)
      (hlhd_halfSpace_ahead ts hleg hhalf) p hp
  obtain ⟨hp12, hp2len⟩ := hb.2
  unfold hlhr_intervalContent
  apply hlhr_slice_legal hexAWStart 1 ts hleg
  omega

theorem hlhd_intervalContent_ne (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    {p : ℕ × ℕ} (hp : p ∈ hlhd_intervals ts hleg) :
    hlhr_intervalContent ts p ≠ [] := by
  have hne : ts ≠ [] := by
    intro hempty
    simp [hlhd_intervals, hempty, hlhr_intervalsAux] at hp
  have hb := hlhr_intervalsAux_bounds (hlhd_height ts hleg) ts.length
    ts.length 0 true (List.length_pos_iff.mpr hne)
      (hlhd_halfSpace_ahead ts hleg hhalf) p hp
  obtain ⟨hp12, hp2len⟩ := hb.2
  unfold hlhr_intervalContent
  have htake : p.2 - p.1 ≤ (ts.drop p.1).length := by
    simp only [List.length_drop]
    omega
  intro hnil
  have hlen := congrArg List.length hnil
  rw [List.length_take_of_le htake] at hlen
  simp only [List.length_nil] at hlen
  omega




theorem hlhd_coreTurns_isLegalSAW
    {m : ℂ} {h : ℤ} {raw : List ℤ}
    (hraw : (ofTurns m h raw).IsLegalSAW) (hrawne : raw ≠ [])
    {entry : ℤ} (hentry : entry = 1 ∨ entry = -1) :
    (ofTurns hexAWStart 1 (hlhd_coreTurns entry raw)).IsLegalSAW := by
  cases raw with
  | nil => exact (hrawne rfl).elim
  | cons t tail =>
      have ht : t = 1 ∨ t = -1 := hraw.1 t (by simp)
      let h' : ℤ := 1 + entry - t
      let m' : ℂ := -halfStep h'
      have hrebase : (ofTurns m' h' (t :: tail)).IsLegalSAW :=
        (hhe_isLegalSAW_rebase m m' h h' (t :: tail)).mpr hraw
      constructor
      · intro u hu
        change u ∈ entry :: tail at hu
        simp only [List.mem_cons] at hu
        rcases hu with hueq | hu
        · rw [hueq]
          exact hentry
        · exact hraw.1 u (List.mem_cons_of_mem t hu)
      · change (verticesAux hexAWStart 1 (entry :: tail)).Nodup
        have hzero : hexAWStart + halfStep 1 = 0 := by
          unfold hexAWStart halfStep
          rw [show (4 : ℤ) = 1 + 3 by norm_num, hexUnit_add_three]
          ring
        have hverts :
            verticesAux hexAWStart 1 (entry :: tail) =
              verticesAux m' h' (t :: tail) := by
          simp only [verticesAux_cons]
          congr 1
          · dsimp [m']
            rw [hzero]
            ring
          · have hh : h' + t = 1 + entry := by
              dsimp [h']
              ring
            rw [hh]
            dsimp [m']
            rw [hzero]
            ring_nf
        rw [hverts]
        exact hrebase.2

theorem hlhd_coreTurns_vertices {raw : List ℤ} (hrawne : raw ≠ [])
    (entry : ℤ) :
    verticesAux hexAWStart 1 (hlhd_coreTurns entry raw) =
      verticesAux (-halfStep (1 + entry - raw.head!))
        (1 + entry - raw.head!) raw := by
  cases raw with
  | nil => exact (hrawne rfl).elim
  | cons t tail =>
      have hzero : hexAWStart + halfStep 1 = 0 := by
        unfold hexAWStart halfStep
        rw [show (4 : ℤ) = 1 + 3 by norm_num, hexUnit_add_three]
        ring
      simp only [hlhd_coreTurns, List.tail_cons, verticesAux_cons,
        List.head!_cons]
      congr 1
      · rw [hzero]
        ring
      · have hh : 1 + entry - t + t = 1 + entry := by ring
        rw [hh, hzero]
        ring_nf

theorem hlhd_endpointTurns_endpointIsLegalSAW
    {core : List ℤ} (hcore : (ofTurns hexAWStart 1 core).IsLegalSAW)
    (exits : Bool) {exitTurn : ℤ}
    (hexit : exitTurn = 1 ∨ exitTurn = -1) :
    (ofTurns hexAWStart 1
      (hlhd_endpointTurns exits exitTurn core)).EndpointIsLegalSAW := by
  cases exits with
  | false =>
      exact hcore.endpointIsLegalSAW
  | true =>
      exact (endpointIsLegalSAW_append_one_iff
        hexAWStart 1 core exitTurn).2 ⟨hcore, hexit⟩



def hlhd_intervalRaw (ts : List ℤ) (p : ℕ × ℕ) : List ℤ :=
  hlhr_intervalContent ts p

noncomputable def hlhd_intervalCore (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) : List ℤ :=
  hlhd_coreTurns
    (hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp))
    (hlhd_intervalRaw ts p)

noncomputable def hlhd_intervalExits (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) : Bool :=
  decide (hlhd_intervalLastEdge ts hleg hhalf p hp ≠ 0)

noncomputable def hlhd_intervalEndpoint (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) : List ℤ :=
  hlhd_endpointTurns (hlhd_intervalExits ts hleg hhalf p hp)
    (hlhd_exitTurn (hlhd_intervalLastEdge ts hleg hhalf p hp))
    (hlhd_intervalCore ts hleg hhalf p hp)

noncomputable def hlhd_intervalTag (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) : HLHDColumnTag :=
  ⟨hlhd_intervalUp ts hleg hhalf p hp,
    hlhd_turnBit (hlhd_intervalRaw ts p).head!,
    hlhd_intervalExits ts hleg hhalf p hp⟩

theorem hlhd_intervalRaw_ne (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hlhd_intervalRaw ts p ≠ [] :=
  hlhd_intervalContent_ne ts hleg hhalf hp

theorem hlhd_intervalRaw_length (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    (hlhd_intervalRaw ts p).length = p.2 - p.1 := by
  unfold hlhd_intervalRaw hlhr_intervalContent
  rw [List.length_take_of_le]
  simp only [List.length_drop]
  exact Nat.sub_le_sub_right
    (hlhd_interval_index_bounds ts hleg hhalf p hp).2 p.1

theorem hlhd_intervalRaw_head_step (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hexInfra_headAccum 1 (ts.take (p.1 + 1)) =
      hexInfra_headAccum 1 (ts.take p.1) +
        (hlhd_intervalRaw ts p).head! := by
  have hb := hlhd_interval_index_bounds ts hleg hhalf p hp
  have hk : p.1 < ts.length := lt_of_lt_of_le hb.1 hb.2
  have hhead : (hlhd_intervalRaw ts p).head! = ts[p.1] := by
    have hdrop : ts.drop p.1 = ts[p.1] :: ts.drop (p.1 + 1) :=
      List.drop_eq_getElem_cons hk
    unfold hlhd_intervalRaw hlhr_intervalContent
    change ((ts.drop p.1).take (p.2 - p.1)).head! = ts[p.1]
    have hdiff : 0 < p.2 - p.1 := Nat.sub_pos_of_lt hb.1
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdiff)
    rw [hn, hdrop]
    rfl
  have htake : ts.take (p.1 + 1) = ts.take p.1 ++ [ts[p.1]] :=
    List.take_succ_eq_append_getElem hk
  simp only [hexInfra_headAccum_eq_add_sum]
  change 1 + (ts.take (p.1 + 1)).sum =
    1 + (ts.take p.1).sum + (hlhd_intervalRaw ts p).head!
  rw [htake]
  rw [hhead]
  simp only [List.sum_append, List.sum_singleton]
  ring

theorem hlhd_interval_entry_unit (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hexUnit (1 + hlhd_entryTurn
        (hlhd_intervalFirstEdge ts hleg hhalf p hp)) =
      if hlhd_intervalUp ts hleg hhalf p hp then
        hexUnit (hexInfra_headAccum 1 (ts.take (p.1 + 1)))
      else -hexUnit (hexInfra_headAccum 1 (ts.take (p.1 + 1))) := by
  let up := hlhd_intervalUp ts hleg hhalf p hp
  let e := hlhd_intervalFirstEdge ts hleg hhalf p hp
  let c := hlhc_prefixCoord ts hleg.1 p.1
  have hunit :
      hexUnit (hexInfra_headAccum 1 (ts.take (p.1 + 1))) =
        hexUnit (hexAWHeading c e) :=
    hlhd_prefix_edge_unit ts hleg p.1
      (lt_of_lt_of_le
        (hlhd_interval_index_bounds ts hleg hhalf p hp).1
        (hlhd_interval_index_bounds ts hleg hhalf p hp).2)
      e (hlhd_intervalFirstEdge_spec ts hleg hhalf p hp)
  have hin : e = 1 ∨ e = 2 :=
    hlhd_intervalFirstEdge_inward ts hleg hhalf p hp
  have hcdir := hlhd_bridge_source_color ts hleg p
    (hlhd_interval_index_bounds ts hleg hhalf p hp).2
    (hlhd_intervalUp_bridge ts hleg hhalf p hp)
  cases hup : up with
  | false =>
      have hc : c.color = .white := by
        simpa [up, hup, c] using hcdir
      simp only [up, hup, Bool.false_eq_true, ↓reduceIte]
      change hexUnit (1 + hlhd_entryTurn e) = -hexUnit _
      rcases hin with he | he
      · rw [he] at hunit ⊢
        rw [hunit]
        have h3 := hexUnit_add_three 0
        simp [c, hc, hlhd_entryTurn, hexAWHeading] at h3 ⊢
        rw [h3]
        ring
      · rw [he] at hunit ⊢
        rw [hunit]
        have h5 := hexUnit_add_three 2
        simp [c, hc, hlhd_entryTurn, hexAWHeading] at h5 ⊢
        rw [h5]
        ring
  | true =>
      have hc : c.color = .black := by
        simpa [up, hup, c] using hcdir
      simp only [up, hup, ↓reduceIte]
      change hexUnit (1 + hlhd_entryTurn e) = hexUnit _
      rcases hin with he | he <;>
        rw [he] at hunit ⊢ <;>
        simpa [c, hc, hlhd_entryTurn, hexAWHeading] using hunit.symm

theorem hlhd_interval_rho (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    let raw := hlhd_intervalRaw ts p
    let entry := hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp)
    let h0 := hexInfra_headAccum 1 (ts.take p.1)
    let h' := 1 + entry - raw.head!
    hhe_rho h0 h' =
      if hlhd_intervalUp ts hleg hhalf p hp then 1 else -1 := by
  dsimp only
  let raw := hlhd_intervalRaw ts p
  let entry := hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp)
  let h0 := hexInfra_headAccum 1 (ts.take p.1)
  let hout := hexInfra_headAccum 1 (ts.take (p.1 + 1))
  let h' := 1 + entry - raw.head!
  let v := halfStep hout
  have hhout : h0 + raw.head! = hout := by
    exact (hlhd_intervalRaw_head_step ts hleg hhalf p hp).symm
  have hhentry : h' + raw.head! = 1 + entry := by
    dsimp [h']
    ring
  have hunit := hlhd_interval_entry_unit ts hleg hhalf p hp
  change hexUnit (1 + entry) =
    if hlhd_intervalUp ts hleg hhalf p hp then hexUnit hout else -hexUnit hout at hunit
  have hentryHalf : halfStep (1 + entry) =
      if hlhd_intervalUp ts hleg hhalf p hp then v else -v := by
    change halfStep (1 + entry) =
      if hlhd_intervalUp ts hleg hhalf p hp then halfStep hout else -halfStep hout
    unfold halfStep
    rw [hunit]
    split <;> ring
  have hshift := hhe_halfStep_shift h0 h' raw.head!
  rw [hhentry, hhout, hentryHalf] at hshift
  have hv : v ≠ 0 := by
    dsimp [v]
    exact hexConcrete_halfStep_ne _
  cases hup : hlhd_intervalUp ts hleg hhalf p hp with
  | false =>
      simp only [hup, Bool.false_eq_true, ↓reduceIte] at hshift ⊢
      apply mul_left_cancel₀ hv
      calc
        v * hhe_rho h0 h' = hhe_rho h0 h' * v := mul_comm _ _
        _ = -v := hshift.symm
        _ = v * (-1) := by ring
  | true =>
      simp only [hup, ↓reduceIte] at hshift ⊢
      apply mul_left_cancel₀ hv
      calc
        v * hhe_rho h0 h' = hhe_rho h0 h' * v := mul_comm _ _
        _ = v := hshift.symm
        _ = v * 1 := by ring

theorem hlhd_intervalCore_vertices_affine (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    let raw := hlhd_intervalRaw ts p
    let up := hlhd_intervalUp ts hleg hhalf p hp
    let source := hlhc_prefixCoord ts hleg.1 p.1
    let m0 := hexInfra_midAccum hexAWStart 1 (ts.take p.1)
    let h0 := hexInfra_headAccum 1 (ts.take p.1)
    verticesAux hexAWStart 1 (hlhd_intervalCore ts hleg hhalf p hp) =
      (verticesAux m0 h0 raw).map (fun z =>
        if up then z - hexAWPos source else hexAWPos source - z) := by
  dsimp only
  let raw := hlhd_intervalRaw ts p
  let up := hlhd_intervalUp ts hleg hhalf p hp
  let source := hlhc_prefixCoord ts hleg.1 p.1
  let m0 := hexInfra_midAccum hexAWStart 1 (ts.take p.1)
  let h0 := hexInfra_headAccum 1 (ts.take p.1)
  let entry := hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp)
  let h' := 1 + entry - raw.head!
  unfold hlhd_intervalCore
  rw [hlhd_coreTurns_vertices (hlhd_intervalRaw_ne ts hleg hhalf p hp)]
  change verticesAux (-halfStep h') h' raw = _
  rw [hhe_verticesAux_rigid0 h0 h' raw m0 (-halfStep h')]
  have hrho := hlhd_interval_rho ts hleg hhalf p hp
  change hhe_rho h0 h' = if up then 1 else -1 at hrho
  have hhstep := hhe_halfStep_shift h0 h' 0
  simp only [add_zero] at hhstep
  rw [hrho] at hhstep
  have hsourcePos := hlhc_prefixCoord_vertex ts hleg.1 p.1
  change m0 + halfStep h0 = hexAWPos source at hsourcePos
  apply List.map_congr_left
  intro z hz
  change hhe_rho h0 h' * (z - m0) + -halfStep h' =
    if up then z - hexAWPos source else hexAWPos source - z
  cases hup : up with
  | false =>
      simp only [hup, Bool.false_eq_true, ↓reduceIte] at hrho hhstep ⊢
      rw [hrho, hhstep, ← hsourcePos]
      ring
  | true =>
      simp only [hup, ↓reduceIte] at hrho hhstep ⊢
      rw [hrho, hhstep, ← hsourcePos]
      ring

theorem hlhd_intervalRaw_vertexPos (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (r : ℕ) (hr : r ≤ (hlhd_intervalRaw ts p).length) :
    hexJordan_vertexPos
        (hexInfra_midAccum hexAWStart 1 (ts.take p.1))
        (hexInfra_headAccum 1 (ts.take p.1))
        (hlhd_intervalRaw ts p) r =
      hexJordan_vertexPos hexAWStart 1 ts (p.1 + r) := by
  have hrn : r ≤ p.2 - p.1 := by
    simpa [hlhd_intervalRaw_length ts hleg hhalf p hp] using hr
  have htake : (hlhd_intervalRaw ts p).take r =
      (ts.drop p.1).take r := by
    unfold hlhd_intervalRaw hlhr_intervalContent
    simp only [List.take_take]
    rw [min_eq_left hrn]
  unfold hexJordan_vertexPos
  rw [htake, List.take_add, hexJordan_midAccum_append,
    hexJordan_headAccum_append]

noncomputable def hlhd_intervalCoords (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (p : ℕ × ℕ) : List HexAWCoord :=
  List.ofFn (fun r : Fin ((hlhd_intervalRaw ts p).length + 1) =>
    hlhc_prefixCoord ts hleg.1 (p.1 + r.val))

theorem hlhd_intervalRaw_vertices_pos (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    verticesAux
        (hexInfra_midAccum hexAWStart 1 (ts.take p.1))
        (hexInfra_headAccum 1 (ts.take p.1))
        (hlhd_intervalRaw ts p) =
      (hlhd_intervalCoords ts hleg p).map hexAWPos := by
  apply List.ext_getElem
  · simp [hlhd_intervalCoords, length_verticesAux]
  · intro r hr hr'
    have hrle : r ≤ (hlhd_intervalRaw ts p).length := by
      rw [length_verticesAux] at hr
      omega
    have hget := hexJordan_verticesAux_getElem?_eq
      (hexInfra_midAccum hexAWStart 1 (ts.take p.1))
      (hexInfra_headAccum 1 (ts.take p.1))
      (hlhd_intervalRaw ts p) r hrle
    rw [List.getElem?_eq_getElem hr, Option.some.injEq] at hget
    rw [List.getElem_map]
    unfold hlhd_intervalCoords
    rw [List.getElem_ofFn]
    rw [hget]
    change hexJordan_vertexPos
        (hexInfra_midAccum hexAWStart 1 (ts.take p.1))
        (hexInfra_headAccum 1 (ts.take p.1))
        (hlhd_intervalRaw ts p) r =
      hexAWPos (hlhc_prefixCoord ts hleg.1 (p.1 + r))
    rw [hlhd_intervalRaw_vertexPos ts hleg hhalf p hp r hrle]
    exact hlhc_prefixCoord_vertex ts hleg.1 (p.1 + r)

noncomputable def hlhd_intervalNormalizedCoords (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    List HexAWCoord :=
  (hlhd_intervalCoords ts hleg p).map
    (hlhd_normalizeCoord (hlhd_intervalUp ts hleg hhalf p hp)
      (hlhc_prefixCoord ts hleg.1 p.1))

@[simp] theorem hlhd_intervalNormalizedCoords_length (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    (hlhd_intervalNormalizedCoords ts hleg hhalf p hp).length =
      (hlhd_intervalRaw ts p).length + 1 := by
  simp [hlhd_intervalNormalizedCoords, hlhd_intervalCoords]

theorem hlhd_intervalNormalizedCoords_getElem (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (r : ℕ) (hr : r < (hlhd_intervalNormalizedCoords ts hleg hhalf p hp).length) :
    (hlhd_intervalNormalizedCoords ts hleg hhalf p hp)[r] =
      hlhd_normalizeCoord (hlhd_intervalUp ts hleg hhalf p hp)
        (hlhc_prefixCoord ts hleg.1 p.1)
        (hlhc_prefixCoord ts hleg.1 (p.1 + r)) := by
  unfold hlhd_intervalNormalizedCoords hlhd_intervalCoords
  rw [List.getElem_map, List.getElem_ofFn]

theorem hlhd_intervalCore_vertices_pos (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    verticesAux hexAWStart 1 (hlhd_intervalCore ts hleg hhalf p hp) =
      (hlhd_intervalNormalizedCoords ts hleg hhalf p hp).map hexAWPos := by
  let up := hlhd_intervalUp ts hleg hhalf p hp
  let source := hlhc_prefixCoord ts hleg.1 p.1
  have hcdir := hlhd_bridge_source_color ts hleg p
    (hlhd_interval_index_bounds ts hleg hhalf p hp).2
    (hlhd_intervalUp_bridge ts hleg hhalf p hp)
  have hsource : if up then source.color = .black else source.color = .white := by
    cases hup : up <;> simpa [up, hup, source] using hcdir
  rw [hlhd_intervalCore_vertices_affine ts hleg hhalf p hp,
    hlhd_intervalRaw_vertices_pos ts hleg hhalf p hp]
  unfold hlhd_intervalNormalizedCoords
  simp only [List.map_map, Function.comp_apply]
  apply List.map_congr_left
  intro c hc
  change (if up then hexAWPos c - hexAWPos source else hexAWPos source - hexAWPos c) =
    hexAWPos (hlhd_normalizeCoord up source c)
  exact (hlhd_normalizeCoord_pos up source c hsource).symm

theorem hlhd_intervalRaw_legal (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    ∀ t ∈ hlhd_intervalRaw ts p, t = 1 ∨ t = -1 := by
  exact (hlhd_interval_legal ts hleg hhalf hp).1

theorem hlhd_intervalCore_isLegalSAW (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    (ofTurns hexAWStart 1
      (hlhd_intervalCore ts hleg hhalf p hp)).IsLegalSAW := by
  exact hlhd_coreTurns_isLegalSAW
    (hlhd_interval_legal ts hleg hhalf hp)
    (hlhd_intervalRaw_ne ts hleg hhalf p hp)
    (hlhd_entryTurn_legal _)

theorem hlhd_intervalCore_prefixCoord (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (r : ℕ) (hr : r ≤ (hlhd_intervalRaw ts p).length) :
    hlhc_prefixCoord (hlhd_intervalCore ts hleg hhalf p hp)
        (hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp).1 r =
      hlhd_normalizeCoord (hlhd_intervalUp ts hleg hhalf p hp)
        (hlhc_prefixCoord ts hleg.1 p.1)
        (hlhc_prefixCoord ts hleg.1 (p.1 + r)) := by
  let core := hlhd_intervalCore ts hleg hhalf p hp
  let hcore := hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp
  let cs := hlhd_intervalNormalizedCoords ts hleg hhalf p hp
  have hcorelen : core.length = (hlhd_intervalRaw ts p).length := by
    exact hlhd_coreTurns_length (hlhd_intervalRaw_ne ts hleg hhalf p hp)
      (hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp))
  have hrCore : r ≤ core.length := by rw [hcorelen]; exact hr
  have hrmap : r < (cs.map hexAWPos).length := by
    simp only [List.length_map]
    change r < cs.length
    dsimp [cs]
    rw [hlhd_intervalNormalizedCoords_length]
    omega
  have hget := hexJordan_verticesAux_getElem?_eq
    hexAWStart 1 core r hrCore
  rw [hlhd_intervalCore_vertices_pos ts hleg hhalf p hp,
    List.getElem?_eq_getElem hrmap, Option.some.injEq] at hget
  rw [List.getElem_map] at hget
  have hcget := hlhd_intervalNormalizedCoords_getElem
    ts hleg hhalf p hp r (by
      rw [hlhd_intervalNormalizedCoords_length]
      omega)
  rw [hcget] at hget
  apply hexAWPos_injective
  exact (hlhc_prefixCoord_vertex core hcore.1 r).symm.trans hget.symm



theorem hlhd_endsAt_lastPrefixEdge (ws : List ℤ)
    (hws : (ofTurns hexAWStart 1 ws).IsLegalSAW) (hne : ws ≠ [])
    (e : Fin 3)
    (he : hexAWNeighbor
      (hlhc_prefixCoord ws hws.1 (ws.length - 1)) e =
        hlhc_prefixCoord ws hws.1 ws.length) :
    (ofTurns hexAWStart 1 ws).EndsAt
      (hexAWMid (hlhc_prefixCoord ws hws.1 (ws.length - 1)) e) := by
  have hnpos : 0 < ws.length := List.length_pos_iff.mpr hne
  have hk : ws.length - 1 < ws.length := by omega
  have hprev := hexEndpoint_vertexPos_eq_nextMid_sub ws (ws.length - 1) hk
  have hprevPos := hlhc_prefixCoord_vertex ws hws.1 (ws.length - 1)
  have hfinalPos := hlhc_prefixCoord_vertex ws hws.1 ws.length
  have hsubadd : ws.length - 1 + 1 = ws.length := by omega
  rw [hsubadd, List.take_length] at hprev
  unfold hexJordan_vertexPos at hprev
  rw [List.take_length] at hfinalPos
  unfold HexWalk.EndsAt
  rw [hexInfra_endMid_eq_midAccum]
  unfold hexAWMid
  rw [he]
  rw [← hprevPos, ← hfinalPos]
  rw [hprev]
  ring

theorem hlhd_neighbor_black_max_edge_zero (c d : HexAWCoord) (e : Fin 3)
    (he : hexAWNeighbor c e = d) (hd : d.color = .black)
    (hdepth : hexAWDepth c ≤ hexAWDepth d) : e = 0 := by
  rcases hlhd_neighbor_depth_cases c e with hinc | hdec | hflat
  · exfalso
    apply hexAWNeighbor_color_ne c e
    rw [he, hd, hinc.2.1]
  · have hdeq := congrArg hexAWDepth he
    rw [hdec.1] at hdeq
    omega
  · exact hflat.2

noncomputable def hlhd_intervalPrevCoord (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) : HexAWCoord :=
  hlhd_normalizeCoord (hlhd_intervalUp ts hleg hhalf p hp)
    (hlhc_prefixCoord ts hleg.1 p.1)
    (hlhc_prefixCoord ts hleg.1 (p.2 - 1))

noncomputable def hlhd_intervalFarCoord (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) : HexAWCoord :=
  hlhd_normalizeCoord (hlhd_intervalUp ts hleg hhalf p hp)
    (hlhc_prefixCoord ts hleg.1 p.1)
    (hlhc_prefixCoord ts hleg.1 p.2)

theorem hlhd_intervalLastEdge_normalized (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hexAWNeighbor (hlhd_intervalPrevCoord ts hleg hhalf p hp)
        (hlhd_intervalLastEdge ts hleg hhalf p hp) =
      hlhd_intervalFarCoord ts hleg hhalf p hp := by
  unfold hlhd_intervalPrevCoord hlhd_intervalFarCoord
  rw [← hlhd_normalizeCoord_neighbor]
  exact congrArg
    (hlhd_normalizeCoord (hlhd_intervalUp ts hleg hhalf p hp)
      (hlhc_prefixCoord ts hleg.1 p.1))
    (hlhd_intervalLastEdge_spec ts hleg hhalf p hp)

theorem hlhd_intervalCore_lastEdge (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    let core := hlhd_intervalCore ts hleg hhalf p hp
    let hcore := hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp
    hexAWNeighbor (hlhc_prefixCoord core hcore.1 (core.length - 1))
        (hlhd_intervalLastEdge ts hleg hhalf p hp) =
      hlhc_prefixCoord core hcore.1 core.length := by
  dsimp only
  let core := hlhd_intervalCore ts hleg hhalf p hp
  let hcore := hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp
  let n := (hlhd_intervalRaw ts p).length
  have hn : 0 < n := List.length_pos_iff.mpr
    (hlhd_intervalRaw_ne ts hleg hhalf p hp)
  have hcorelen : core.length = n := by
    exact hlhd_coreTurns_length (hlhd_intervalRaw_ne ts hleg hhalf p hp)
      (hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp))
  have hnval : n = p.2 - p.1 :=
    hlhd_intervalRaw_length ts hleg hhalf p hp
  have hprevIndex : p.1 + (n - 1) = p.2 - 1 := by omega
  have hfarIndex : p.1 + n = p.2 := by
    have hb := hlhd_interval_index_bounds ts hleg hhalf p hp
    omega
  rw [hcorelen]
  rw [hlhd_intervalCore_prefixCoord ts hleg hhalf p hp (n - 1) (by omega),
    hlhd_intervalCore_prefixCoord ts hleg hhalf p hp n le_rfl,
    hprevIndex, hfarIndex]
  exact hlhd_intervalLastEdge_normalized ts hleg hhalf p hp

theorem hlhd_intervalCore_endsAt (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    (ofTurns hexAWStart 1 (hlhd_intervalCore ts hleg hhalf p hp)).EndsAt
      (hexAWMid (hlhd_intervalPrevCoord ts hleg hhalf p hp)
        (hlhd_intervalLastEdge ts hleg hhalf p hp)) := by
  let core := hlhd_intervalCore ts hleg hhalf p hp
  let hcore := hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp
  have hne : core ≠ [] := by
    dsimp [core, hlhd_intervalCore, hlhd_coreTurns]
    simp
  have hend := hlhd_endsAt_lastPrefixEdge core hcore hne
    (hlhd_intervalLastEdge ts hleg hhalf p hp)
    (hlhd_intervalCore_lastEdge ts hleg hhalf p hp)
  have hcorelen : core.length = (hlhd_intervalRaw ts p).length :=
    hlhd_coreTurns_length (hlhd_intervalRaw_ne ts hleg hhalf p hp)
      (hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp))
  have hnval := hlhd_intervalRaw_length ts hleg hhalf p hp
  have hidx : p.1 + (core.length - 1) = p.2 - 1 := by
    have hb := hlhd_interval_index_bounds ts hleg hhalf p hp
    omega
  rw [hlhd_intervalCore_prefixCoord ts hleg hhalf p hp
    (core.length - 1) (by rw [hcorelen]; omega), hidx] at hend
  exact hend

theorem hlhd_intervalEndpoint_endpointIsLegalSAW (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    (ofTurns hexAWStart 1
      (hlhd_intervalEndpoint ts hleg hhalf p hp)).EndpointIsLegalSAW := by
  exact hlhd_endpointTurns_endpointIsLegalSAW
    (hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp)
    (hlhd_intervalExits ts hleg hhalf p hp)
    (hlhd_exitTurn_legal _)

theorem hlhd_interval_decode (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hlhd_decodeColumn (hlhd_intervalTag ts hleg hhalf p hp)
        (hlhd_intervalEndpoint ts hleg hhalf p hp) =
      hlhd_intervalRaw ts p := by
  exact hlhd_decodeColumn_encode
    (hlhd_intervalRaw_ne ts hleg hhalf p hp)
    (hlhd_intervalRaw_legal ts hleg hhalf p hp)
    (hlhd_intervalUp ts hleg hhalf p hp)
    (hlhd_intervalExits ts hleg hhalf p hp)
    (hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp))
    (hlhd_exitTurn (hlhd_intervalLastEdge ts hleg hhalf p hp))

theorem hlhd_intervalEndpoint_length (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    (hlhd_intervalEndpoint ts hleg hhalf p hp).length =
        (hlhd_intervalRaw ts p).length ∨
      (hlhd_intervalEndpoint ts hleg hhalf p hp).length =
        (hlhd_intervalRaw ts p).length + 1 := by
  have hcore := hlhd_coreTurns_length
    (hlhd_intervalRaw_ne ts hleg hhalf p hp)
    (hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp))
  have hout := hlhd_endpointTurns_length
    (hlhd_intervalExits ts hleg hhalf p hp)
    (hlhd_exitTurn (hlhd_intervalLastEdge ts hleg hhalf p hp))
    (hlhd_intervalCore ts hleg hhalf p hp)
  simpa [hlhd_intervalEndpoint, hlhd_intervalCore, hcore] using hout

@[simp] theorem hlhd_intervalCore_length (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    (hlhd_intervalCore ts hleg hhalf p hp).length =
      (hlhd_intervalRaw ts p).length :=
  hlhd_coreTurns_length (hlhd_intervalRaw_ne ts hleg hhalf p hp)
    (hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp))

theorem hlhd_intervalEndpoint_index_le_core (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    {k : ℕ}
    (hk : k < (hlhd_intervalEndpoint ts hleg hhalf p hp).length) :
    k ≤ (hlhd_intervalCore ts hleg hhalf p hp).length := by
  rw [hlhd_intervalCore_length]
  cases hexits : hlhd_intervalExits ts hleg hhalf p hp <;>
    simp [hlhd_intervalEndpoint, hlhd_endpointTurns, hexits] at hk <;>
    omega

theorem hlhd_intervalEndpoint_prefixCoord_eq_core (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (k : ℕ)
    (hk : k ≤ (hlhd_intervalCore ts hleg hhalf p hp).length) :
    hlhc_prefixCoord (hlhd_intervalEndpoint ts hleg hhalf p hp)
        (hlhd_intervalEndpoint_endpointIsLegalSAW
          ts hleg hhalf p hp).1 k =
      hlhc_prefixCoord (hlhd_intervalCore ts hleg hhalf p hp)
        (hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp).1 k := by
  apply hexAWPos_injective
  rw [← hlhc_prefixCoord_vertex
      (hlhd_intervalEndpoint ts hleg hhalf p hp)
      (hlhd_intervalEndpoint_endpointIsLegalSAW ts hleg hhalf p hp).1 k,
    ← hlhc_prefixCoord_vertex
      (hlhd_intervalCore ts hleg hhalf p hp)
      (hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp).1 k]
  have htake :
      (hlhd_intervalEndpoint ts hleg hhalf p hp).take k =
        (hlhd_intervalCore ts hleg hhalf p hp).take k := by
    cases hexits : hlhd_intervalExits ts hleg hhalf p hp
    · simp [hlhd_intervalEndpoint, hlhd_endpointTurns, hexits]
    · simp only [hlhd_intervalEndpoint, hlhd_endpointTurns, hexits,
        ↓reduceIte]
      exact List.take_append_of_le_length hk
  rw [htake]


noncomputable def hlhd_spans (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) : List ℝ :=
  hlhr_intervalSpans (hlhd_height ts hleg) (hlhd_intervals ts hleg)

theorem hlhd_spans_pairwise (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg) :
    (hlhd_spans ts hleg).Pairwise (· > ·) := by
  by_cases hempty : ts = []
  · simp [hempty, hlhd_spans, hlhd_intervals,
      hlhr_intervalsAux, hlhr_intervalSpans]
  · exact (hlhr_intervalSpans_ordered (hlhd_height ts hleg) ts.length
      ts.length 0 true (List.length_pos_iff.mpr hempty)
      (hlhd_halfSpace_ahead ts hleg hhalf)).1

theorem hlhd_spans_pos (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg) :
    ∀ w ∈ hlhd_spans ts hleg, 0 < w := by
  by_cases hempty : ts = []
  · simp [hempty, hlhd_spans, hlhd_intervals,
      hlhr_intervalsAux, hlhr_intervalSpans]
  · exact (hlhr_intervalSpans_ordered (hlhd_height ts hleg) ts.length
      ts.length 0 true (List.length_pos_iff.mpr hempty)
      (hlhd_halfSpace_ahead ts hleg hhalf)).2.1


noncomputable def hlhd_delta (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (p : ℕ × ℕ) : ℤ :=
  hlhd_depth ts hleg p.2 - hlhd_depth ts hleg p.1


noncomputable def hlhd_width (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (p : ℕ × ℕ) : ℕ :=
  (hlhd_delta ts hleg p).natAbs



theorem hlhd_normalized_depth_bounds (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (p : ℕ × ℕ) {up : Bool}
    (hb : HLHRBridgeInterval (hlhd_height ts hleg) up p)
    {k : ℕ} (hklo : p.1 ≤ k) (hkhi : k ≤ p.2) :
    0 ≤ hexAWDepth (hlhd_normalizeCoord up
        (hlhc_prefixCoord ts hleg.1 p.1)
        (hlhc_prefixCoord ts hleg.1 k)) ∧
      hexAWDepth (hlhd_normalizeCoord up
        (hlhc_prefixCoord ts hleg.1 p.1)
        (hlhc_prefixCoord ts hleg.1 k)) ≤
          (hlhd_width ts hleg p : ℤ) := by
  have hbounds := hlhd_bridge_depth_bounds ts hleg p hb hklo hkhi
  have hend := hb.2.1 p.2 hb.1 le_rfl
  unfold hlhd_width hlhd_delta
  rw [hlhd_normalizeCoord_depth]
  cases up with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, hlhr_signed,
        hlhd_height, hlhd_depth] at hbounds hend ⊢
      have hksourceR :
          (hexAWDepth (hlhc_prefixCoord ts hleg.1 k) : ℝ) ≤
            hexAWDepth (hlhc_prefixCoord ts hleg.1 p.1) := by
        linarith [hbounds.1]
      have hendkR :
          (hexAWDepth (hlhc_prefixCoord ts hleg.1 p.2) : ℝ) ≤
            hexAWDepth (hlhc_prefixCoord ts hleg.1 k) := by
        linarith [hbounds.2]
      have hendR :
          (hexAWDepth (hlhc_prefixCoord ts hleg.1 p.2) : ℝ) <
            hexAWDepth (hlhc_prefixCoord ts hleg.1 p.1) := by
        linarith
      have hksource : hexAWDepth (hlhc_prefixCoord ts hleg.1 k) ≤
          hexAWDepth (hlhc_prefixCoord ts hleg.1 p.1) := by
        exact_mod_cast hksourceR
      have hendk : hexAWDepth (hlhc_prefixCoord ts hleg.1 p.2) ≤
          hexAWDepth (hlhc_prefixCoord ts hleg.1 k) := by
        exact_mod_cast hendkR
      have hendZ : hexAWDepth (hlhc_prefixCoord ts hleg.1 p.2) <
          hexAWDepth (hlhc_prefixCoord ts hleg.1 p.1) := by
        exact_mod_cast hendR
      rw [Int.ofNat_natAbs_of_nonpos (by omega)]
      omega
  | true =>
      simp only [↓reduceIte, hlhr_signed, hlhd_height, hlhd_depth] at hbounds hend ⊢
      have hsourcek : hexAWDepth (hlhc_prefixCoord ts hleg.1 p.1) ≤
          hexAWDepth (hlhc_prefixCoord ts hleg.1 k) := by
        exact_mod_cast hbounds.1
      have hkend : hexAWDepth (hlhc_prefixCoord ts hleg.1 k) ≤
          hexAWDepth (hlhc_prefixCoord ts hleg.1 p.2) := by
        exact_mod_cast hbounds.2
      have hendZ : hexAWDepth (hlhc_prefixCoord ts hleg.1 p.1) <
          hexAWDepth (hlhc_prefixCoord ts hleg.1 p.2) := by
        exact_mod_cast hend
      rw [Int.natAbs_of_nonneg (by omega)]
      omega



theorem hlhd_normalized_depth_pos (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (p : ℕ × ℕ) {up : Bool}
    (hb : HLHRBridgeInterval (hlhd_height ts hleg) up p)
    {k : ℕ} (hklo : p.1 < k) (hkhi : k ≤ p.2) :
    0 < hexAWDepth (hlhd_normalizeCoord up
      (hlhc_prefixCoord ts hleg.1 p.1)
      (hlhc_prefixCoord ts hleg.1 k)) := by
  have hstrict := hb.2.1 k hklo hkhi
  rw [hlhd_normalizeCoord_depth]
  cases up with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, hlhr_signed,
        hlhd_height, hlhd_depth] at hstrict ⊢
      have hz : hexAWDepth (hlhc_prefixCoord ts hleg.1 k) <
          hexAWDepth (hlhc_prefixCoord ts hleg.1 p.1) := by
        exact_mod_cast (show
          (hexAWDepth (hlhc_prefixCoord ts hleg.1 k) : ℝ) <
            hexAWDepth (hlhc_prefixCoord ts hleg.1 p.1) by linarith)
      omega
  | true =>
      simp only [↓reduceIte, hlhr_signed, hlhd_height,
        hlhd_depth] at hstrict ⊢
      have hz : hexAWDepth (hlhc_prefixCoord ts hleg.1 p.1) <
          hexAWDepth (hlhc_prefixCoord ts hleg.1 k) := by
        exact_mod_cast hstrict
      omega

theorem hlhd_normalized_endpoint_depth (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (p : ℕ × ℕ) {up : Bool}
    (hb : HLHRBridgeInterval (hlhd_height ts hleg) up p) :
    hexAWDepth (hlhd_normalizeCoord up
        (hlhc_prefixCoord ts hleg.1 p.1)
        (hlhc_prefixCoord ts hleg.1 p.2)) =
      hlhd_width ts hleg p := by
  have hend := hb.2.1 p.2 hb.1 le_rfl
  unfold hlhd_width hlhd_delta
  rw [hlhd_normalizeCoord_depth]
  cases up with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, hlhr_signed,
        hlhd_height, hlhd_depth] at hend ⊢
      have hendR :
          (hexAWDepth (hlhc_prefixCoord ts hleg.1 p.2) : ℝ) <
            hexAWDepth (hlhc_prefixCoord ts hleg.1 p.1) := by
        linarith
      have hendZ : hexAWDepth (hlhc_prefixCoord ts hleg.1 p.2) <
          hexAWDepth (hlhc_prefixCoord ts hleg.1 p.1) := by
        exact_mod_cast hendR
      rw [Int.ofNat_natAbs_of_nonpos (by omega)]
      omega
  | true =>
      simp only [↓reduceIte, hlhr_signed, hlhd_height, hlhd_depth] at hend ⊢
      have hendZ : hexAWDepth (hlhc_prefixCoord ts hleg.1 p.1) <
          hexAWDepth (hlhc_prefixCoord ts hleg.1 p.2) := by
        exact_mod_cast hend
      rw [Int.natAbs_of_nonneg (by omega)]

theorem hlhd_intervalFarCoord_depth (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hexAWDepth (hlhd_intervalFarCoord ts hleg hhalf p hp) =
      hlhd_width ts hleg p := by
  exact hlhd_normalized_endpoint_depth ts hleg p
    (hlhd_intervalUp_bridge ts hleg hhalf p hp)

theorem hlhd_intervalPrevCoord_depth_le (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hexAWDepth (hlhd_intervalPrevCoord ts hleg hhalf p hp) ≤
      hexAWDepth (hlhd_intervalFarCoord ts hleg hhalf p hp) := by
  have hb := hlhd_interval_index_bounds ts hleg hhalf p hp
  have hprev := hlhd_normalized_depth_bounds ts hleg p
    (hlhd_intervalUp_bridge ts hleg hhalf p hp)
    (k := p.2 - 1) (by omega) (by omega)
  rw [hlhd_intervalFarCoord_depth ts hleg hhalf p hp]
  exact hprev.2

theorem hlhd_intervalLastEdge_zero_of_far_black (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (hblack : (hlhd_intervalFarCoord ts hleg hhalf p hp).color = .black) :
    hlhd_intervalLastEdge ts hleg hhalf p hp = 0 := by
  exact hlhd_neighbor_black_max_edge_zero _ _ _
    (hlhd_intervalLastEdge_normalized ts hleg hhalf p hp) hblack
    (hlhd_intervalPrevCoord_depth_le ts hleg hhalf p hp)

noncomputable def hlhd_intervalTopCoord (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) : HexAWCoord :=
  let far := hlhd_intervalFarCoord ts hleg hhalf p hp
  if far.color = .white then far else hexAWNeighbor far 0

theorem hlhd_intervalTopCoord_white (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    (hlhd_intervalTopCoord ts hleg hhalf p hp).color = .white := by
  let far := hlhd_intervalFarCoord ts hleg hhalf p hp
  change (if far.color = .white then far else hexAWNeighbor far 0).color = .white
  by_cases hc : far.color = .white
  · simp [hc]
  · rw [if_neg hc]
    rcases far with ⟨i, j, color⟩
    cases color <;> simp_all [hexAWNeighbor]

theorem hlhd_neighbor_zero_depth (c : HexAWCoord) :
    hexAWDepth (hexAWNeighbor c 0) = hexAWDepth c := by
  rcases c with ⟨i, j, color⟩
  cases color <;> simp [hexAWNeighbor, hexAWDepth, hexAWLong]

theorem hlhd_intervalTopCoord_depth (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hexAWDepth (hlhd_intervalTopCoord ts hleg hhalf p hp) =
      hlhd_width ts hleg p := by
  let far := hlhd_intervalFarCoord ts hleg hhalf p hp
  by_cases hc : far.color = .white
  · simpa [hlhd_intervalTopCoord, far, hc] using
      hlhd_intervalFarCoord_depth ts hleg hhalf p hp
  · rw [hlhd_intervalTopCoord, show
        hlhd_intervalFarCoord ts hleg hhalf p hp = far from rfl, if_neg hc,
      hlhd_neighbor_zero_depth]
    exact hlhd_intervalFarCoord_depth ts hleg hhalf p hp

theorem hlhd_intervalExits_false_of_far_black (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (hblack : (hlhd_intervalFarCoord ts hleg hhalf p hp).color = .black) :
    hlhd_intervalExits ts hleg hhalf p hp = false := by
  unfold hlhd_intervalExits
  rw [hlhd_intervalLastEdge_zero_of_far_black ts hleg hhalf p hp hblack]
  decide

theorem hlhd_intervalFarCoord_white_of_exits (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (hexits : hlhd_intervalExits ts hleg hhalf p hp = true) :
    (hlhd_intervalFarCoord ts hleg hhalf p hp).color = .white := by
  cases hc : (hlhd_intervalFarCoord ts hleg hhalf p hp).color with
  | white => rfl
  | black =>
      have hf := hlhd_intervalExits_false_of_far_black
        ts hleg hhalf p hp hc
      rw [hexits] at hf
      contradiction

theorem hlhd_hexUnit_add_eq_of_eq (h k t : ℤ)
    (hu : hexUnit h = hexUnit k) :
    hexUnit (h + t) = hexUnit (k + t) := by
  rw [hhe_hexUnit_add, hhe_hexUnit_add, hu]



theorem hlhd_exit_heading_unit (c d : HexAWCoord) (e : Fin 3)
    (he : hexAWNeighbor c e = d) (hd : d.color = .white)
    (hin : e = 1 ∨ e = 2) :
    hexUnit (hexAWHeading c e + hlhd_exitTurn e) =
      hexUnit (hexAWHeading d 0) := by
  rcases c with ⟨i, j, color⟩
  rcases d with ⟨i', j', color'⟩
  rcases hin with rfl | rfl <;>
    cases color <;> cases color' <;>
    simp [hexAWNeighbor, hexAWHeading, hlhd_exitTurn] at he hd ⊢
  all_goals
    rw [show (7 : ℤ) = 1 + 6 by norm_num, hexUnit_add_six]



theorem hlhd_append_exit_endsAt (ws : List ℤ)
    (c d : HexAWCoord) (e : Fin 3)
    (hend : (ofTurns hexAWStart 1 ws).EndsAt (hexAWMid c e))
    (hhead : hexUnit (hexInfra_headAccum 1 ws) =
      hexUnit (hexAWHeading c e))
    (he : hexAWNeighbor c e = d) (hd : d.color = .white)
    (hin : e = 1 ∨ e = 2) :
    (ofTurns hexAWStart 1 (ws ++ [hlhd_exitTurn e])).EndsAt
      (hexAWMid d 0) := by
  have hhead' := hlhd_hexUnit_add_eq_of_eq
    (hexInfra_headAccum 1 ws) (hexAWHeading c e)
    (hlhd_exitTurn e) hhead
  have hexit := hlhd_exit_heading_unit c d e he hd hin
  have hfirst : halfStep (hexInfra_headAccum 1 ws) =
      halfStep (hexAWHeading c e) := by
    unfold halfStep
    rw [hhead]
  have hsecond :
      halfStep (hexInfra_headAccum 1 ws + hlhd_exitTurn e) =
        halfStep (hexAWHeading d 0) := by
    unfold halfStep
    rw [hhead', hexit]
  have htoFar : hexAWMid c e + halfStep (hexAWHeading c e) =
      hexAWPos d := by
    have hstep := hexAWNeighborPos_eq_mid_add c e
    rw [he] at hstep
    exact hstep.symm
  have htoTop : hexAWPos d + halfStep (hexAWHeading d 0) =
      hexAWMid d 0 := by
    have hstep := hexAWMid_sub_pos_eq_halfStep d 0
    rw [← hstep]
    ring
  unfold HexWalk.EndsAt at hend ⊢
  rw [hexInfra_endMid_eq_midAccum] at hend ⊢
  rw [hexCyclic_midAccum_append_single, hend, hfirst, hsecond]
  linear_combination htoFar + htoTop

theorem hlhd_intervalCore_finalCoord (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    let core := hlhd_intervalCore ts hleg hhalf p hp
    let hcore := hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp
    hlhc_prefixCoord core hcore.1 core.length =
      hlhd_intervalFarCoord ts hleg hhalf p hp := by
  dsimp only
  let core := hlhd_intervalCore ts hleg hhalf p hp
  have hcorelen : core.length = (hlhd_intervalRaw ts p).length :=
    hlhd_coreTurns_length (hlhd_intervalRaw_ne ts hleg hhalf p hp)
      (hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp))
  have hnval := hlhd_intervalRaw_length ts hleg hhalf p hp
  have hb := hlhd_interval_index_bounds ts hleg hhalf p hp
  rw [hlhd_intervalCore_prefixCoord ts hleg hhalf p hp core.length (by
    rw [hcorelen])]
  unfold hlhd_intervalFarCoord
  congr 2
  omega

theorem hlhd_intervalCore_prevCoord (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    let core := hlhd_intervalCore ts hleg hhalf p hp
    let hcore := hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp
    hlhc_prefixCoord core hcore.1 (core.length - 1) =
      hlhd_intervalPrevCoord ts hleg hhalf p hp := by
  dsimp only
  let core := hlhd_intervalCore ts hleg hhalf p hp
  have hcorelen : core.length = (hlhd_intervalRaw ts p).length :=
    hlhd_coreTurns_length (hlhd_intervalRaw_ne ts hleg hhalf p hp)
      (hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp))
  have hnval := hlhd_intervalRaw_length ts hleg hhalf p hp
  have hb := hlhd_interval_index_bounds ts hleg hhalf p hp
  rw [hlhd_intervalCore_prefixCoord ts hleg hhalf p hp
    (core.length - 1) (by rw [hcorelen]; omega)]
  unfold hlhd_intervalPrevCoord
  congr 2
  omega

theorem hlhd_intervalCore_heading_unit (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hexUnit (hexInfra_headAccum 1
        (hlhd_intervalCore ts hleg hhalf p hp)) =
      hexUnit (hexAWHeading
        (hlhd_intervalPrevCoord ts hleg hhalf p hp)
        (hlhd_intervalLastEdge ts hleg hhalf p hp)) := by
  let core := hlhd_intervalCore ts hleg hhalf p hp
  let hcore := hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp
  have hne : core ≠ [] := by
    dsimp [core, hlhd_intervalCore, hlhd_coreTurns]
    simp
  have hk : core.length - 1 < core.length := by
    exact Nat.sub_lt (List.length_pos_iff.mpr hne) (by omega)
  have hu := hlhd_prefix_edge_unit core hcore
    (core.length - 1) hk
    (hlhd_intervalLastEdge ts hleg hhalf p hp)
    (hlhd_intervalCore_lastEdge ts hleg hhalf p hp)
  have hsucc : core.length - 1 + 1 = core.length := by omega
  rw [hsucc, List.take_length,
    hlhd_intervalCore_prevCoord ts hleg hhalf p hp] at hu
  exact hu

theorem hlhd_fin3_inward_of_ne_zero (e : Fin 3) (he : e ≠ 0) :
    e = 1 ∨ e = 2 := by
  fin_cases e <;> simp_all

theorem hlhd_fin3_zero_of_decide_ne_false (e : Fin 3)
    (he : decide (e ≠ 0) = false) : e = 0 := by
  by_contra hne
  simp [hne] at he

theorem hlhd_intervalCore_endsAt_top_of_noExit (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (hexits : hlhd_intervalExits ts hleg hhalf p hp = false) :
    (ofTurns hexAWStart 1
      (hlhd_intervalCore ts hleg hhalf p hp)).EndsAt
        (hexAWMid (hlhd_intervalTopCoord ts hleg hhalf p hp) 0) := by
  let prev := hlhd_intervalPrevCoord ts hleg hhalf p hp
  let far := hlhd_intervalFarCoord ts hleg hhalf p hp
  let e := hlhd_intervalLastEdge ts hleg hhalf p hp
  have he0 : e = 0 := by
    apply hlhd_fin3_zero_of_decide_ne_false
    simpa only [e, hlhd_intervalExits] using hexits
  have hfar : hexAWNeighbor prev 0 = far := by
    simpa only [prev, far, e, he0] using
      hlhd_intervalLastEdge_normalized ts hleg hhalf p hp
  have hend := hlhd_intervalCore_endsAt ts hleg hhalf p hp
  have hmid : hexAWMid prev e =
      hexAWMid (hlhd_intervalTopCoord ts hleg hhalf p hp) 0 := by
    rw [he0]
    by_cases hc : far.color = .white
    · rw [hlhd_intervalTopCoord, show
          hlhd_intervalFarCoord ts hleg hhalf p hp = far from rfl,
        if_pos hc, ← hfar]
      exact (hexAWMid_neighbor prev 0).symm
    · rw [hlhd_intervalTopCoord, show
          hlhd_intervalFarCoord ts hleg hhalf p hp = far from rfl,
        if_neg hc, ← hfar, hexAWNeighbor_invol]
  simpa only [prev, e, hmid] using hend



theorem hlhd_intervalEndpoint_endsAt (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    (ofTurns hexAWStart 1
      (hlhd_intervalEndpoint ts hleg hhalf p hp)).EndsAt
        (hexAWMid (hlhd_intervalTopCoord ts hleg hhalf p hp) 0) := by
  cases hexits : hlhd_intervalExits ts hleg hhalf p hp with
  | false =>
      simpa [hlhd_intervalEndpoint, hlhd_endpointTurns, hexits] using
        hlhd_intervalCore_endsAt_top_of_noExit
          ts hleg hhalf p hp hexits
  | true =>
      let core := hlhd_intervalCore ts hleg hhalf p hp
      let prev := hlhd_intervalPrevCoord ts hleg hhalf p hp
      let far := hlhd_intervalFarCoord ts hleg hhalf p hp
      let e := hlhd_intervalLastEdge ts hleg hhalf p hp
      have hwhite : far.color = .white := by
        exact hlhd_intervalFarCoord_white_of_exits
          ts hleg hhalf p hp hexits
      have hene : e ≠ 0 := by
        intro he0
        unfold hlhd_intervalExits at hexits
        simp [e, he0] at hexits
      have hin : e = 1 ∨ e = 2 :=
        hlhd_fin3_inward_of_ne_zero e hene
      have hend := hlhd_append_exit_endsAt core prev far e
        (hlhd_intervalCore_endsAt ts hleg hhalf p hp)
        (hlhd_intervalCore_heading_unit ts hleg hhalf p hp)
        (hlhd_intervalLastEdge_normalized ts hleg hhalf p hp)
        hwhite hin
      have htop : hlhd_intervalTopCoord ts hleg hhalf p hp = far := by
        simp [hlhd_intervalTopCoord, far, hwhite]
      simpa [hlhd_intervalEndpoint, hlhd_endpointTurns, hexits,
        core, e, htop] using hend

theorem hlhd_intervalCore_depth_bounds (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (r : ℕ)
    (hr : r ≤ (hlhd_intervalCore ts hleg hhalf p hp).length) :
    0 ≤ hexAWDepth (hlhc_prefixCoord
        (hlhd_intervalCore ts hleg hhalf p hp)
        (hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp).1 r) ∧
      hexAWDepth (hlhc_prefixCoord
        (hlhd_intervalCore ts hleg hhalf p hp)
        (hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp).1 r) ≤
        (hlhd_width ts hleg p : ℤ) := by
  have hraw : (hlhd_intervalRaw ts p).length = p.2 - p.1 :=
    hlhd_intervalRaw_length ts hleg hhalf p hp
  have hbounds := hlhd_interval_index_bounds ts hleg hhalf p hp
  rw [hlhd_intervalCore_prefixCoord ts hleg hhalf p hp r (by
    simpa only [hlhd_intervalCore_length] using hr)]
  apply hlhd_normalized_depth_bounds ts hleg p
    (hlhd_intervalUp_bridge ts hleg hhalf p hp)
  · omega
  · rw [hlhd_intervalCore_length, hraw] at hr
    omega

theorem hlhd_intervalCore_white_depth_pos (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (r : ℕ)
    (hr : r ≤ (hlhd_intervalCore ts hleg hhalf p hp).length)
    (hwhite : (hlhc_prefixCoord
      (hlhd_intervalCore ts hleg hhalf p hp)
      (hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp).1 r).color =
        .white) :
    0 < hexAWDepth (hlhc_prefixCoord
      (hlhd_intervalCore ts hleg hhalf p hp)
      (hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp).1 r) := by
  have hraw : (hlhd_intervalRaw ts p).length = p.2 - p.1 :=
    hlhd_intervalRaw_length ts hleg hhalf p hp
  have hbounds := hlhd_interval_index_bounds ts hleg hhalf p hp
  by_cases hr0 : r = 0
  · subst r
    have hsource := hlhd_intervalCore_prefixCoord
      ts hleg hhalf p hp 0 (by omega)
    simp only [Nat.add_zero] at hsource
    rw [hlhd_interval_source_normalizes ts hleg hhalf p hp] at hsource
    rw [hsource] at hwhite
    simp [hexAWOriginCoord] at hwhite
  · rw [hlhd_intervalCore_prefixCoord ts hleg hhalf p hp r (by
      simpa only [hlhd_intervalCore_length] using hr)]
    apply hlhd_normalized_depth_pos ts hleg p
      (hlhd_intervalUp_bridge ts hleg hhalf p hp)
    · omega
    · rw [hlhd_intervalCore_length, hraw] at hr
      omega

theorem hlhd_white_depth_mem_horizontal (T : ℕ) (c : HexAWCoord)
    (hwhite : c.color = .white) (hpos : 0 < hexAWDepth c)
    (hupper : hexAWDepth c ≤ T) :
    0 ≤ hexAWBookRe2 c ∧ hexAWBookRe2 c ≤ 3 * T := by
  simp only [hexAWBookRe2, hwhite]
  constructor <;> omega

theorem hlhd_span_eq_width (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (p : ℕ × ℕ) :
    hlhr_intervalSpan (hlhd_height ts hleg) p = hlhd_width ts hleg p := by
  simp only [hlhr_intervalSpan, hlhd_height, hlhd_width, hlhd_delta]
  rw [← Int.cast_sub]
  rw [← hlhr_natAbs_cast]

theorem hlhd_width_pos_of_span_pos (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (p : ℕ × ℕ)
    (hp : 0 < hlhr_intervalSpan (hlhd_height ts hleg) p) :
    0 < hlhd_width ts hleg p := by
  rw [hlhd_span_eq_width] at hp
  exact_mod_cast hp

theorem hlhd_width_gt_of_span_gt (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (p q : ℕ × ℕ)
    (hpq : hlhr_intervalSpan (hlhd_height ts hleg) p >
      hlhr_intervalSpan (hlhd_height ts hleg) q) :
    hlhd_width ts hleg p > hlhd_width ts hleg q := by
  rw [hlhd_span_eq_width, hlhd_span_eq_width] at hpq
  exact_mod_cast hpq

theorem hlhd_interval_bounds (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg) :
    ∀ p ∈ hlhd_intervals ts hleg, p.1 < p.2 ∧ p.2 ≤ ts.length := by
  intro p hp
  have hne : ts ≠ [] := by
    intro hempty
    simp [hlhd_intervals, hempty, hlhr_intervalsAux] at hp
  exact hlhr_intervalsAux_bounds (hlhd_height ts hleg) ts.length
    ts.length 0 true (List.length_pos_iff.mpr hne)
      (hlhd_halfSpace_ahead ts hleg hhalf) p hp |>.2



noncomputable def hlhd_bridge (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : {p // p ∈ hlhd_intervals ts hleg}) : HexBridge where
  width := hlhd_width ts hleg p.1
  width_pos := by
    apply hlhd_width_pos_of_span_pos ts hleg p.1
    exact hlhd_spans_pos ts hleg hhalf _ (by
      simpa [hlhd_spans, hlhr_intervalSpans] using
        List.mem_map_of_mem p.2)
  content := hlhr_intervalContent ts p.1
  content_ne := by
    obtain ⟨hp12, hp2len⟩ := hlhd_interval_bounds ts hleg hhalf p.1 p.2
    unfold hlhr_intervalContent
    have htake : p.1.2 - p.1.1 ≤ (ts.drop p.1.1).length := by
      simp only [List.length_drop]
      omega
    intro hnil
    have hlen := congrArg List.length hnil
    rw [List.length_take_of_le htake] at hlen
    simp only [List.length_nil] at hlen
    omega

noncomputable def hlhd_bridgeList (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg) : List HexBridge :=
  (hlhd_intervals ts hleg).attach.map (hlhd_bridge ts hleg hhalf)

theorem hlhd_bridgeList_widths (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg) :
    (hlhd_bridgeList ts hleg hhalf).map HexBridge.width =
      (hlhd_intervals ts hleg).map (hlhd_width ts hleg) := by
  unfold hlhd_bridgeList
  simp [hlhd_bridge]

theorem hlhd_bridgeList_contents (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg) :
    ((hlhd_bridgeList ts hleg hhalf).map HexBridge.content).flatten = ts := by
  simpa [hlhd_bridgeList, hlhd_bridge, Function.comp_def,
    hlhd_intervalTurns, hlhr_intervalTurns] using
    hlhd_intervals_reconstruct ts hleg hhalf

theorem hlhd_bridgeList_strict (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg) :
    StrictDecreasingWidths (hlhd_bridgeList ts hleg hhalf) := by
  have hreal := hlhd_spans_pairwise ts hleg hhalf
  have hintervals : (hlhd_intervals ts hleg).Pairwise
      (fun p q => hlhr_intervalSpan (hlhd_height ts hleg) p >
        hlhr_intervalSpan (hlhd_height ts hleg) q) := by
    unfold hlhd_spans hlhr_intervalSpans at hreal
    exact List.pairwise_map.mp hreal
  have hwidths :
      ((hlhd_intervals ts hleg).map (hlhd_width ts hleg)).Pairwise
        (· > ·) :=
    List.pairwise_map.mpr (hintervals.imp (fun hpq =>
      hlhd_width_gt_of_span_gt ts hleg _ _ hpq))
  rw [← hlhd_bridgeList_widths ts hleg hhalf] at hwidths
  simpa [StrictDecreasingWidths, List.pairwise_map] using hwidths


noncomputable def hlhd_contentHalf (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg) : HexHWContentHalf :=
  ⟨hlhd_bridgeList ts hleg hhalf, hlhd_bridgeList_strict ts hleg hhalf⟩

@[simp] theorem hlhd_contentHalf_turns (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg) :
    hhc_halfTurns (hlhd_contentHalf ts hleg hhalf) = ts :=
  hlhd_bridgeList_contents ts hleg hhalf

theorem hlhd_interval_width_pos (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    0 < hlhd_width ts hleg p := by
  simpa [hlhd_bridge] using
    (hlhd_bridge ts hleg hhalf ⟨p, hp⟩).width_pos

theorem hlhd_neighbor_white_of_black {c d : HexAWCoord} {e : Fin 3}
    (hc : c.color = .black) (he : hexAWNeighbor c e = d) :
    d.color = .white := by
  subst d
  rcases c with ⟨i, j, color⟩
  cases color <;> simp_all
  fin_cases e <;> rfl




theorem hlhd_intervalEndpoint_mid_incident_horizontal (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (k : ℕ)
    (hk : k < (hlhd_intervalEndpoint ts hleg hhalf p hp).length) :
    ∃ c : HexAWCoord, ∃ e : Fin 3,
      hexInfra_midAccum hexAWStart 1
          ((hlhd_intervalEndpoint ts hleg hhalf p hp).take k) =
        hexAWMid c e ∧
      0 ≤ hexAWBookRe2 c ∧
        hexAWBookRe2 c ≤ 3 * hlhd_width ts hleg p := by
  have hwidth := hlhd_interval_width_pos ts hleg hhalf p hp
  by_cases hk0 : k = 0
  · subst k
    refine ⟨hexAWOriginCoord, 0, ?_, ?_⟩
    · simp
    · simp [hexAWBookRe2, hexAWOriginCoord, hexAWDepth, hexAWLong]
      omega
  · let out := hlhd_intervalEndpoint ts hleg hhalf p hp
    let hout := hlhd_intervalEndpoint_endpointIsLegalSAW ts hleg hhalf p hp
    let core := hlhd_intervalCore ts hleg hhalf p hp
    let hcore := hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hkcore : k ≤ core.length := by
      exact hlhd_intervalEndpoint_index_le_core ts hleg hhalf p hp hk
    have hkprevcore : k - 1 ≤ core.length := by omega
    have hkprevout : k - 1 < out.length := by
      change k - 1 <
        (hlhd_intervalEndpoint ts hleg hhalf p hp).length
      omega
    obtain ⟨e, he⟩ := hlhc_prefixCoord_adjacent_legal
      out hout.1 (k - 1) hkprevout
    have hsucc : k - 1 + 1 = k := by omega
    rw [hsucc] at he
    have hmid := hlhd_midAccum_prefixEdge out hout.1 k hkpos
      (Nat.le_of_lt (show k < out.length by exact hk)) e he
    let a := hlhc_prefixCoord out hout.1 (k - 1)
    let b := hlhc_prefixCoord out hout.1 k
    change hexAWNeighbor a e = b at he
    change hexInfra_midAccum hexAWStart 1 (out.take k) =
      hexAWMid a e at hmid
    have ha : a = hlhc_prefixCoord core hcore.1 (k - 1) := by
      exact hlhd_intervalEndpoint_prefixCoord_eq_core
        ts hleg hhalf p hp (k - 1) hkprevcore
    have hb : b = hlhc_prefixCoord core hcore.1 k := by
      exact hlhd_intervalEndpoint_prefixCoord_eq_core
        ts hleg hhalf p hp k hkcore
    by_cases haw : a.color = .white
    · have hawCore :
          (hlhc_prefixCoord core hcore.1 (k - 1)).color = .white := by
        simpa only [ha] using haw
      have hpos := hlhd_intervalCore_white_depth_pos
        ts hleg hhalf p hp (k - 1) hkprevcore hawCore
      have hupper :=
        (hlhd_intervalCore_depth_bounds
          ts hleg hhalf p hp (k - 1) hkprevcore).2
      refine ⟨a, e, hmid, ?_⟩
      simpa only [ha] using hlhd_white_depth_mem_horizontal
        (hlhd_width ts hleg p) _ hawCore hpos hupper
    · have hablack : a.color = .black := by
        cases hc : a.color <;> simp_all
      have hbwhite : b.color = .white :=
        hlhd_neighbor_white_of_black hablack he
      have hbwhiteCore :
          (hlhc_prefixCoord core hcore.1 k).color = .white := by
        simpa only [hb] using hbwhite
      have hpos := hlhd_intervalCore_white_depth_pos
        ts hleg hhalf p hp k hkcore hbwhiteCore
      have hupper :=
        (hlhd_intervalCore_depth_bounds
          ts hleg hhalf p hp k hkcore).2
      have hswap : hexAWMid a e = hexAWMid b e := by
        rw [← he]
        exact (hexAWMid_neighbor a e).symm
      refine ⟨b, e, hmid.trans hswap, ?_⟩
      simpa only [hb] using hlhd_white_depth_mem_horizontal
        (hlhd_width ts hleg p) _ hbwhiteCore hpos hupper

noncomputable def hlhd_intervalMidCoord (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (k : Fin (hlhd_intervalEndpoint ts hleg hhalf p hp).length) :
    HexAWCoord :=
  Classical.choose (hlhd_intervalEndpoint_mid_incident_horizontal
    ts hleg hhalf p hp k.1 k.2)

noncomputable def hlhd_intervalMidEdge (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (k : Fin (hlhd_intervalEndpoint ts hleg hhalf p hp).length) :
    Fin 3 :=
  Classical.choose (Classical.choose_spec
    (hlhd_intervalEndpoint_mid_incident_horizontal
      ts hleg hhalf p hp k.1 k.2))

theorem hlhd_intervalMid_spec (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (k : Fin (hlhd_intervalEndpoint ts hleg hhalf p hp).length) :
    hexInfra_midAccum hexAWStart 1
        ((hlhd_intervalEndpoint ts hleg hhalf p hp).take k.1) =
      hexAWMid (hlhd_intervalMidCoord ts hleg hhalf p hp k)
        (hlhd_intervalMidEdge ts hleg hhalf p hp k) ∧
    0 ≤ hexAWBookRe2 (hlhd_intervalMidCoord ts hleg hhalf p hp k) ∧
      hexAWBookRe2 (hlhd_intervalMidCoord ts hleg hhalf p hp k) ≤
        3 * hlhd_width ts hleg p := by
  unfold hlhd_intervalMidCoord hlhd_intervalMidEdge
  exact Classical.choose_spec (Classical.choose_spec
    (hlhd_intervalEndpoint_mid_incident_horizontal
      ts hleg hhalf p hp k.1 k.2))



noncomputable def hlhd_midpointColumnWalk (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    HLHCMidpointColumnWalk (hlhd_width ts hleg p)
      (hlhd_intervalEndpoint ts hleg hhalf p hp) where
  legal := hlhd_intervalEndpoint_endpointIsLegalSAW ts hleg hhalf p hp
  midCoord := hlhd_intervalMidCoord ts hleg hhalf p hp
  midEdge := hlhd_intervalMidEdge ts hleg hhalf p hp
  incident := fun k => (hlhd_intervalMid_spec ts hleg hhalf p hp k).1
  horizontal := fun k => (hlhd_intervalMid_spec ts hleg hhalf p hp k).2
  topCoord := hlhd_intervalTopCoord ts hleg hhalf p hp
  top_white := hlhd_intervalTopCoord_white ts hleg hhalf p hp
  top_depth := hlhd_intervalTopCoord_depth ts hleg hhalf p hp
  endsAt := hlhd_intervalEndpoint_endsAt ts hleg hhalf p hp


theorem hlhd_intervalEndpoint_mem_topAtWidth (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    HexCSTopWalkAtWidth (hlhd_width ts hleg p)
      (hlhd_interval_width_pos ts hleg hhalf p hp)
      (hlhd_intervalEndpoint ts hleg hhalf p hp) := by
  exact (hlhd_midpointColumnWalk ts hleg hhalf p hp).mem_topAtWidth
    (hlhd_interval_width_pos ts hleg hhalf p hp)

end

end StatMech.Universality

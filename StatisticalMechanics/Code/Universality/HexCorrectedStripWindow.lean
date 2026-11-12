/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.Universality.HexCorrectedStripExit
import Code.Universality.HexEndpointLocalGeometry
import Code.Onsager.PeriodicTurnClosure

namespace StatMech.Universality

open Complex Function HexWalk
open scoped BigOperators
open StatMech.Onsager

noncomputable section




noncomputable def hexCSHeadingFin (h : ℤ) : Fin 6 :=
  (ZMod.finEquiv 6).symm (h : ZMod 6)

@[simp] theorem hexCSHeadingFin_zero : hexCSHeadingFin 0 = 0 := by
  apply (ZMod.finEquiv 6).injective
  simp [hexCSHeadingFin]

@[simp] theorem hexCSHeadingFin_one : hexCSHeadingFin 1 = 1 := by
  apply (ZMod.finEquiv 6).injective
  simp [hexCSHeadingFin]

theorem hexCSHeadingFin_add (h k : ℤ) :
    hexCSHeadingFin (h + k) = hexCSHeadingFin h + hexCSHeadingFin k := by
  apply (ZMod.finEquiv 6).injective
  simp [hexCSHeadingFin]

theorem hexCSHeadingFin_dvd (h : ℤ) :
    (6 : ℤ) ∣ h - (hexCSHeadingFin h).val := by
  have hz : hexCSHeadingFin h = (h : ZMod 6) :=
    (ZMod.finEquiv 6).apply_symm_apply _
  have hvn : (hexCSHeadingFin h).val = (h : ZMod 6).val :=
    congrArg Fin.val hz
  have hvcast : (((h : ZMod 6).val : ℕ) : ℤ) = h % 6 :=
    ZMod.val_intCast (n := 6) h
  have hv : ((hexCSHeadingFin h).val : ℤ) = h % 6 :=
    (congrArg (fun n : ℕ => (n : ℤ)) hvn).trans hvcast
  refine ⟨h / 6, ?_⟩
  rw [hv, Int.emod_def]
  ring

theorem hexCSHeadingFin_unit (h : ℤ) :
    hexUnit h = hexUnit (hexCSHeadingFin h).val := by
  exact (hexUnit_eq_iff_mod _ _).2 (hexCSHeadingFin_dvd h)

theorem hexCSHeadingFin_turn (h t : ℤ) (ht : t = 1 ∨ t = -1) :
    hexCSHeadingFin (h + t) =
      hexHeadingTurn (hexCSHeadingFin h) t := by
  rcases ht with rfl | rfl
  · rw [hexHeadingTurn, if_pos rfl, hexCSHeadingFin_add]
    simp
  · rw [hexHeadingTurn, if_neg (by norm_num), hexCSHeadingFin_add]
    apply (ZMod.finEquiv 6).injective
    simp [hexCSHeadingFin, sub_eq_add_neg]



noncomputable def hexCSBrickDirections (h : ℤ) (ts : List ℤ) :
    List (Fin 4) :=
  (headingsAux h ts).map
    (fun q => hexBrickDir (hexCSHeadingFin q))

@[simp] theorem hexCSBrickDirections_nil (h : ℤ) :
    hexCSBrickDirections h [] = [hexBrickDir (hexCSHeadingFin h)] := rfl

@[simp] theorem hexCSBrickDirections_cons (h t : ℤ) (ts : List ℤ) :
    hexCSBrickDirections h (t :: ts) =
      hexBrickDir (hexCSHeadingFin h) ::
        hexCSBrickDirections (h + t) ts := rfl

@[simp] theorem hexCSBrickDirections_length (h : ℤ) (ts : List ℤ) :
    (hexCSBrickDirections h ts).length = ts.length + 1 := by
  simp [hexCSBrickDirections, length_headingsAux]

theorem hexCSBrickDirections_ne_nil (h : ℤ) (ts : List ℤ) :
    hexCSBrickDirections h ts ≠ [] := by
  intro he
  have := congrArg List.length he
  simp at this

@[simp] theorem hexCSBrickDirections_head (h : ℤ) (ts : List ℤ) :
    (hexCSBrickDirections h ts).head! =
      hexBrickDir (hexCSHeadingFin h) := by
  cases ts <;> rfl

@[simp] theorem hexCSBrickDirections_getLast (h : ℤ) (ts : List ℤ) :
    (hexCSBrickDirections h ts).getLast! =
      hexBrickDir (hexCSHeadingFin (hexInfra_headAccum h ts)) := by
  induction ts generalizing h with
  | nil => rfl
  | cons t ts ih =>
      rw [hexCSBrickDirections_cons]
      have htail : hexCSBrickDirections (h + t) ts ≠ [] :=
        hexCSBrickDirections_ne_nil _ _
      rw [ons_getLast!_eq_getLast _ (List.cons_ne_nil _ _),
        List.getLast_cons htail,
        ← ons_getLast!_eq_getLast _ htail, ih]
      rfl


theorem hexCS_brick_open_telescope (h : ℤ) (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    2 * ts.sum + 3 * ons_openTurnSum (hexCSBrickDirections h ts) =
      hexBrickTurnPotential
          (hexCSHeadingFin (hexInfra_headAccum h ts)) -
        hexBrickTurnPotential (hexCSHeadingFin h) := by
  induction ts generalizing h with
  | nil => simp [hexInfra_headAccum]
  | cons t ts ih =>
      have ht : t = 1 ∨ t = -1 := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      have hlocal := hexBrick_local_turn_identity
        (hexCSHeadingFin h) t ht
      rw [← hexCSHeadingFin_turn h t ht] at hlocal
      have hdirs : hexCSBrickDirections (h + t) ts ≠ [] :=
        hexCSBrickDirections_ne_nil _ _
      obtain ⟨d, ds, hd⟩ := List.exists_cons_of_ne_nil hdirs
      have hdval : d = hexBrickDir (hexCSHeadingFin (h + t)) := by
        have heq := congrArg List.head! hd
        rw [hexCSBrickDirections_head] at heq
        simpa using heq.symm
      rw [hexCSBrickDirections_cons, hd,
        ons_openTurnSum_cons_cons, ← hd]
      rw [hdval]
      simp only [List.sum_cons, hexInfra_headAccum_cons]
      have hi := ih (h + t) htail
      omega





def hexCSEdgeOfHeading (c : HexAWCoord) (h : Fin 6) : Fin 3 :=
  match c.color, h.val with
  | .black, 4 => 0
  | .black, 0 => 1
  | .black, 2 => 2
  | .white, 1 => 0
  | .white, 3 => 1
  | .white, 5 => 2
  | _, _ => 0


def HexCSHeadingFits (c : HexAWCoord) (h : Fin 6) : Prop :=
  match c.color with
  | .black => h.val % 2 = 0
  | .white => h.val % 2 = 1

theorem hexCSHeadingFits_start :
    HexCSHeadingFits hexCSOutsideStartCoord (hexCSHeadingFin 1) := by
  simp [HexCSHeadingFits, hexCSOutsideStartCoord]

theorem hexCSEdgeOfHeading_mod (c : HexAWCoord) (h : Fin 6)
    (hfit : HexCSHeadingFits c h) :
    hexAWHeadingMod c (hexCSEdgeOfHeading c h) = h := by
  rcases c with ⟨i, j, color⟩
  cases color <;> fin_cases h <;>
    simp [HexCSHeadingFits, hexCSEdgeOfHeading,
      hexAWHeadingMod] at hfit ⊢

theorem hexAWHeadingMod_unit (c : HexAWCoord) (e : Fin 3) :
    hexUnit (hexAWHeading c e) =
      hexUnit (hexAWHeadingMod c e).val := by
  rcases c with ⟨i, j, color⟩
  cases color <;> fin_cases e <;>
    simp [hexAWHeading, hexAWHeadingMod]
  rw [show (7 : ℤ) = 1 + 6 by norm_num, hexUnit_add_six]

theorem hexCSEdgeOfHeading_halfStep
    (c : HexAWCoord) (h0 : ℤ)
    (hfit : HexCSHeadingFits c (hexCSHeadingFin h0)) :
    halfStep h0 =
    halfStep (hexAWHeading c
        (hexCSEdgeOfHeading c (hexCSHeadingFin h0))) := by
  have hu := hexCSHeadingFin_unit h0
  have hm := hexCSEdgeOfHeading_mod c (hexCSHeadingFin h0) hfit
  have he := hexAWHeadingMod_unit c
    (hexCSEdgeOfHeading c (hexCSHeadingFin h0))
  calc
    halfStep h0 = (1 / 2 : ℂ) *
        hexUnit (hexCSHeadingFin h0).val := by
      unfold halfStep
      rw [hu]
    _ = (1 / 2 : ℂ) *
        hexUnit (hexAWHeadingMod c
          (hexCSEdgeOfHeading c (hexCSHeadingFin h0))).val := by rw [hm]
    _ = halfStep (hexAWHeading c
        (hexCSEdgeOfHeading c (hexCSHeadingFin h0))) := by
      unfold halfStep
      rw [he]

theorem hexCSHeadingFits_step (c : HexAWCoord) (h : Fin 6) (t : ℤ)
    (hfit : HexCSHeadingFits c h) (ht : t = 1 ∨ t = -1) :
    HexCSHeadingFits
      (hexAWNeighbor c (hexCSEdgeOfHeading c h))
      (hexHeadingTurn h t) := by
  rcases c with ⟨i, j, color⟩
  rcases ht with rfl | rfl <;> cases color <;> fin_cases h <;>
    simp [HexCSHeadingFits, hexCSEdgeOfHeading, hexAWNeighbor,
      hexHeadingTurn] at hfit ⊢



def hexCSCoordPath : HexAWCoord → Fin 6 → List ℤ → List HexAWCoord
  | c, h, [] => [c, hexAWNeighbor c (hexCSEdgeOfHeading c h)]
  | c, h, t :: ts =>
      c :: hexCSCoordPath
        (hexAWNeighbor c (hexCSEdgeOfHeading c h))
        (hexHeadingTurn h t) ts

@[simp] theorem hexCSCoordPath_length
    (c : HexAWCoord) (h : Fin 6) (ts : List ℤ) :
    (hexCSCoordPath c h ts).length = ts.length + 2 := by
  induction ts generalizing c h with
  | nil => rfl
  | cons t ts ih => simp [hexCSCoordPath, ih]



theorem hexCSCoordPath_brick
    (c : HexAWCoord) (h0 : ℤ) (ts : List ℤ)
    (hfit : HexCSHeadingFits c (hexCSHeadingFin h0))
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    (hexCSCoordPath c (hexCSHeadingFin h0) ts).map
        (fun q => hexBrickPos q - hexBrickPos c) =
      ons_pathVertices (hexCSBrickDirections h0 ts) := by
  induction ts generalizing c h0 with
  | nil =>
      simp only [hexCSCoordPath, hexCSBrickDirections_nil,
        ons_pathVertices_cons, ons_pathVertices_nil, List.map_cons,
        List.map_singleton, sub_self]
      have hs := hexBrickPos_neighbor c
        (hexCSEdgeOfHeading c (hexCSHeadingFin h0))
      rw [hexCSEdgeOfHeading_mod c (hexCSHeadingFin h0) hfit] at hs
      simp only [List.cons.injEq, List.map_cons, List.map_nil,
        List.cons.injEq, and_true]
      exact ⟨trivial, by simpa using (sub_eq_iff_eq_add').2 hs⟩
  | cons t ts ih =>
      have ht : t = 1 ∨ t = -1 := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      let e := hexCSEdgeOfHeading c (hexCSHeadingFin h0)
      let c' := hexAWNeighbor c e
      have hfit' : HexCSHeadingFits c'
          (hexCSHeadingFin (h0 + t)) := by
        rw [hexCSHeadingFin_turn h0 t ht]
        exact hexCSHeadingFits_step c (hexCSHeadingFin h0) t hfit ht
      have hi := ih c' (h0 + t) hfit' htail
      have hs := hexBrickPos_neighbor c e
      have hemod : hexAWHeadingMod c e = hexCSHeadingFin h0 :=
        hexCSEdgeOfHeading_mod c (hexCSHeadingFin h0) hfit
      rw [hemod] at hs
      change hexBrickPos c' = hexBrickPos c +
        StatMech.Onsager.BaseCase.stepOf
          (hexBrickDir (hexCSHeadingFin h0)) at hs
      simp only [hexCSCoordPath, hexCSBrickDirections_cons,
        ons_pathVertices_cons, List.map_cons, sub_self,
        List.cons.injEq, true_and]
      rw [← hexCSHeadingFin_turn h0 t ht]
      change List.map (fun q => hexBrickPos q - hexBrickPos c)
          (hexCSCoordPath c' (hexCSHeadingFin (h0 + t)) ts) = _
      rw [← hi]
      simp only [List.map_map, Function.comp_apply]
      apply List.map_congr_left
      intro q hq
      change hexBrickPos q - hexBrickPos c =
        StatMech.Onsager.BaseCase.stepOf
            (hexBrickDir (hexCSHeadingFin h0)) +
          (hexBrickPos q - hexBrickPos c')
      rw [hs]
      abel



theorem hexCSCoordPath_pos
    (c : HexAWCoord) (m : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hfit : HexCSHeadingFits c (hexCSHeadingFin h0))
    (hmid : m = hexAWMid c
      (hexCSEdgeOfHeading c (hexCSHeadingFin h0)))
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    (hexCSCoordPath c (hexCSHeadingFin h0) ts).map hexAWPos =
      hexAWPos c :: verticesAux m h0 ts := by
  induction ts generalizing c m h0 with
  | nil =>
      simp only [hexCSCoordPath, List.map_cons, List.map_singleton,
        verticesAux]
      have hh := hexCSEdgeOfHeading_halfStep c h0 hfit
      have hnext : hexAWPos (hexAWNeighbor c
          (hexCSEdgeOfHeading c (hexCSHeadingFin h0))) =
          m + halfStep h0 := by
        calc
          hexAWPos (hexAWNeighbor c
              (hexCSEdgeOfHeading c (hexCSHeadingFin h0))) =
              hexAWMid c (hexCSEdgeOfHeading c
                (hexCSHeadingFin h0)) +
                halfStep (hexAWHeading c
                  (hexCSEdgeOfHeading c (hexCSHeadingFin h0))) :=
            hexAWNeighborPos_eq_mid_add c _
          _ = m + halfStep h0 := by rw [← hmid, ← hh]
      rw [hnext]
      rfl
  | cons t ts ih =>
      have ht : t = 1 ∨ t = -1 := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      let e := hexCSEdgeOfHeading c (hexCSHeadingFin h0)
      let c' := hexAWNeighbor c e
      let m' := m + halfStep h0 + halfStep (h0 + t)
      have hfit' : HexCSHeadingFits c'
          (hexCSHeadingFin (h0 + t)) := by
        rw [hexCSHeadingFin_turn h0 t ht]
        exact hexCSHeadingFits_step c (hexCSHeadingFin h0) t hfit ht
      have hcur : m + halfStep h0 = hexAWPos c' := by
        have hh := hexCSEdgeOfHeading_halfStep c h0 hfit
        change m = hexAWMid c e at hmid
        calc
          m + halfStep h0 = hexAWMid c e +
              halfStep (hexAWHeading c e) := by rw [hmid, hh]
          _ = hexAWPos (hexAWNeighbor c e) :=
            (hexAWNeighborPos_eq_mid_add c e).symm
          _ = hexAWPos c' := rfl
      have hmid' : m' = hexAWMid c'
          (hexCSEdgeOfHeading c' (hexCSHeadingFin (h0 + t))) := by
        have hh := hexCSEdgeOfHeading_halfStep c' (h0 + t) hfit'
        have hm := hexAWMid_sub_pos_eq_halfStep c'
          (hexCSEdgeOfHeading c' (hexCSHeadingFin (h0 + t)))
        rw [← hh] at hm
        change m + halfStep h0 + halfStep (h0 + t) = _
        calc
          m + halfStep h0 + halfStep (h0 + t) =
              hexAWPos c' + halfStep (h0 + t) := by rw [hcur]
          _ = hexAWMid c' (hexCSEdgeOfHeading c'
              (hexCSHeadingFin (h0 + t))) := by
            exact ((sub_eq_iff_eq_add').1 hm).symm
      have hi := ih c' m' (h0 + t) hfit' hmid' htail
      simp only [hexCSCoordPath, List.map_cons, verticesAux_cons,
        List.cons.injEq, true_and]
      change (hexCSCoordPath c' (hexHeadingTurn
        (hexCSHeadingFin h0) t) ts).map hexAWPos = _
      rw [← hexCSHeadingFin_turn h0 t ht]
      simpa only [m', hcur] using hi





theorem hexCS_mem_of_two_incident_mids
    {T L : ℕ} (c : HexAWCoord) (e f : Fin 3)
    (hef : e ≠ f)
    (he : hexAWMid c e ∈ hexCSMids T L)
    (hf : hexAWMid c f ∈ hexCSMids T L) :
    c ∈ hexCSVertexSet T L := by
  rw [hexCSMids, Finset.mem_biUnion] at he
  obtain ⟨v, _, hv⟩ := he
  rw [Finset.mem_image] at hv
  obtain ⟨g, _, hg⟩ := hv
  rcases (hexAWMid_eq_iff c v.1 e g).mp hg.symm with
      ⟨hvc, _⟩ | ⟨hvn, hge⟩
  · exact hvc ▸ v.2
  · by_contra hc
    let E : HexCSIncidence T L := ⟨v, e⟩
    have hboundary : E ∈ hexCSBoundaryIncidences T L := by
      rw [hexCS_mem_boundary_iff]
      unfold hexCSIsInterior E
      simpa [E, hvn, hexAWNeighbor_invol] using hc
    have houter : hexAWNeighbor E.vtx.1 E.edge = c := by
      simp only [E]
      rw [hvn, hexAWNeighbor_invol]
    have hfm : hexAWMid (hexAWNeighbor E.vtx.1 E.edge) f ∈
        hexCSMids T L := by simpa [houter] using hf
    have hfe : f = E.edge :=
      (hexCSOutsideBoundary_mid_mem_iff E hboundary f).mp hfm
    exact hef (by simpa [E] using hfe.symm)



theorem hexCS_prefixCoord_mem
    {T L : ℕ} {hT : 0 < T} (ts : List ℤ)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion)
    (k : ℕ) (hk : k < ts.length) :
    hexEndpointPrefixCoord ts hadm.1.1 k ∈ hexCSVertexSet T L := by
  let c := hexEndpointPrefixCoord ts hadm.1.1 k
  have hlegalTake : ∀ u ∈ ts.take k, u = 1 ∨ u = -1 := by
    intro u hu
    exact hadm.1.1 u (List.mem_of_mem_take hu)
  have hvertex : hexInfra_midAccum hexAWStart 1 (ts.take k) +
      halfStep (hexInfra_headAccum 1 (ts.take k)) = hexAWPos c := by
    simpa [hexJordan_vertexPos, c] using
      hexEndpointPrefixCoord_pos ts hadm.1.1 k
  obtain ⟨e, he⟩ := hexEndpoint_mid_incident_aw
    (ts.take k) c hlegalTake hvertex
  let t := ts[k]
  have ht : t = 1 ∨ t = -1 :=
    hadm.1.1 t (List.getElem_mem hk)
  obtain ⟨f, hfe, hf⟩ := hexEndpoint_next_mid_of_forward_vertex
    (ts.take k) t c e hlegalTake ht he hvertex
  have htake : ts.take k ++ [t] = ts.take (k + 1) :=
    (List.take_succ_eq_append_getElem hk).symm
  rw [htake] at hf
  have hpassE : PassesThrough hexAWStart 1 ts (hexAWMid c e) := by
    rw [← he]
    exact hexEndpoint_prefix_mid_mem hexAWStart 1 ts k (by omega)
  have hpassF : PassesThrough hexAWStart 1 ts (hexAWMid c f) := by
    rw [← hf]
    exact hexEndpoint_prefix_mid_mem hexAWStart 1 ts (k + 1) (by omega)
  exact hexCS_mem_of_two_incident_mids c e f hfe.symm
    (hadm.2 _ hpassE) (hadm.2 _ hpassF)



theorem hexCS_endpointVertex_inside
    {T L : ℕ} {hT : 0 < T} (ts : List ℤ)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion)
    (x : ℂ) (hx : x ∈ (ofTurns hexAWStart 1 ts).endpointVertices) :
    ∃ c : HexAWCoord, c ∈ hexCSVertexSet T L ∧ x = hexAWPos c := by
  change x ∈ (verticesAux hexAWStart 1 ts).dropLast at hx
  rw [List.mem_iff_getElem] at hx
  obtain ⟨k, hk, hx⟩ := hx
  have hklt : k < ts.length := by
    rw [List.length_dropLast, length_verticesAux] at hk
    omega
  have hfullLen : k < (verticesAux hexAWStart 1 ts).length := by
    rw [length_verticesAux]
    omega
  have hget := hexJordan_verticesAux_getElem?_eq
    hexAWStart 1 ts k (by omega)
  rw [List.getElem?_eq_getElem hfullLen, Option.some.injEq] at hget
  have hxpos : x = hexJordan_vertexPos hexAWStart 1 ts k := by
    unfold hexJordan_vertexPos
    rw [← hget, ← hx]
    exact List.getElem_dropLast hk
  let c := hexEndpointPrefixCoord ts hadm.1.1 k
  refine ⟨c, hexCS_prefixCoord_mem ts hadm k hklt, ?_⟩
  rw [hxpos, hexEndpointPrefixCoord_pos ts hadm.1.1 k]



theorem hexCS_outer_ne_outsideStart
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (hne : e ≠ hexCSStartIncidence T L hT) :
    hexAWNeighbor e.vtx.1 e.edge ≠ hexCSOutsideStartCoord := by
  intro hout
  have hmidMem : hexAWMid hexCSOutsideStartCoord e.edge ∈
      hexCSMids T L := by
    rw [← hout, hexAWMid_neighbor]
    rw [hexCSMids, Finset.mem_biUnion]
    refine ⟨e.vtx, Finset.mem_univ _, ?_⟩
    rw [Finset.mem_image]
    exact ⟨e.edge, Finset.mem_univ _, rfl⟩
  have hedge : e.edge = 0 :=
    (hexCSOutsideStart_mid_mem_iff T L hT e.edge).mp hmidMem
  have hcoord : e.vtx.1 = hexAWOriginCoord := by
    have h := congrArg (fun c => hexAWNeighbor c e.edge) hout
    change hexAWNeighbor (hexAWNeighbor e.vtx.1 e.edge) e.edge =
      hexAWNeighbor hexCSOutsideStartCoord e.edge at h
    rw [hexAWNeighbor_invol, hedge] at h
    simpa [hexCSOutsideStartCoord, hexAWNeighbor] using h
  apply hne
  rw [HexIncidence.mk.injEq]
  exact ⟨Subtype.ext hcoord, hedge⟩



theorem hexCS_full_isSAW
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (ts : List ℤ) (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    (ofTurns hexAWStart 1 ts).IsSAW := by
  apply hexEndpoint_isSAW_of_lookahead_fresh
    hexAWStart 1 ts hadm.1.2
  intro hlook
  obtain ⟨c, hc, hpos⟩ :=
    hexCS_endpointVertex_inside ts ⟨hadm.1, hadm.2.1⟩ _ hlook
  have hexit := hexCS_endpoint_boundary_exit e ts he hne hadm
  have houter : hexInfra_midAccum hexAWStart 1 ts +
      halfStep (hexInfra_headAccum 1 ts) =
      hexAWPos (hexAWNeighbor e.vtx.1 e.edge) := by
    calc
      _ = hexAWMid e.vtx.1 e.edge +
          halfStep (hexCSCanonicalHeading e) := hexit
      _ = hexAWMid e.vtx.1 e.edge +
          halfStep (hexAWHeading e.vtx.1 e.edge) := by
        rw [hexCSCanonicalHeading_halfStep]
      _ = hexAWPos (hexAWNeighbor e.vtx.1 e.edge) :=
        (hexAWNeighborPos_eq_mid_add e.vtx.1 e.edge).symm
  have hcoord : c = hexAWNeighbor e.vtx.1 e.edge := by
    apply hexAWPos_injective
    rw [← hpos, houter]
  exact (hexCSOutsideBoundary_not_mem e he) (hcoord ▸ hc)



theorem hexCS_outsideStart_not_mem_vertices
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (ts : List ℤ) (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    hexAWPos hexCSOutsideStartCoord ∉
      (ofTurns hexAWStart 1 ts).vertices := by
  rw [hexEndpoint_vertices_eq_append_lookahead]
  simp only [List.mem_append, List.mem_singleton, not_or]
  constructor
  · intro hs
    obtain ⟨c, hc, hpos⟩ :=
      hexCS_endpointVertex_inside ts ⟨hadm.1, hadm.2.1⟩ _ hs
    have hcoord : c = hexCSOutsideStartCoord :=
      hexAWPos_injective (hpos.symm)
    rw [hcoord, hexCS_mem_vertexSet_iff] at hc
    simp [hexCSOutsideStartCoord, hexCSInStrip, hexAWBookRe2,
      hexAWDepth, hexAWLong] at hc
  · intro hs
    have hexit := hexCS_endpoint_boundary_exit e ts he hne hadm
    have hposOuter : hexInfra_midAccum hexAWStart 1 ts +
        halfStep (hexInfra_headAccum 1 ts) =
        hexAWPos (hexAWNeighbor e.vtx.1 e.edge) := by
      calc
        _ = hexAWMid e.vtx.1 e.edge +
            halfStep (hexCSCanonicalHeading e) := hexit
        _ = hexAWMid e.vtx.1 e.edge +
            halfStep (hexAWHeading e.vtx.1 e.edge) := by
          rw [hexCSCanonicalHeading_halfStep]
        _ = hexAWPos (hexAWNeighbor e.vtx.1 e.edge) :=
          (hexAWNeighborPos_eq_mid_add e.vtx.1 e.edge).symm
    have hcoord : hexAWNeighbor e.vtx.1 e.edge =
        hexCSOutsideStartCoord := by
      apply hexAWPos_injective
      rw [← hposOuter]
      exact hs.symm
    exact hexCS_outer_ne_outsideStart e hne hcoord

@[simp] theorem hexCSCoordPath_start_pos (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    (hexCSCoordPath hexCSOutsideStartCoord
        (hexCSHeadingFin 1) ts).map hexAWPos =
      hexAWPos hexCSOutsideStartCoord ::
        verticesAux hexAWStart 1 ts := by
  apply hexCSCoordPath_pos hexCSOutsideStartCoord hexAWStart 1 ts
    hexCSHeadingFits_start
  · rw [hexCSHeadingFin_one]
    change hexAWStart = hexAWMid hexCSOutsideStartCoord 0
    exact hexCSOutsideStart_mid_zero.symm
  · exact hlegal


theorem hexCSCoordPath_start_nodup
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (ts : List ℤ) (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    (hexCSCoordPath hexCSOutsideStartCoord
      (hexCSHeadingFin 1) ts).Nodup := by
  have hfull := hexCS_full_isSAW e ts he hne hadm
  change (verticesAux hexAWStart 1 ts).Nodup at hfull
  have hout := hexCS_outsideStart_not_mem_vertices e ts he hne hadm
  change hexAWPos hexCSOutsideStartCoord ∉
    verticesAux hexAWStart 1 ts at hout
  have hmapped : ((hexCSCoordPath hexCSOutsideStartCoord
      (hexCSHeadingFin 1) ts).map hexAWPos).Nodup := by
    rw [hexCSCoordPath_start_pos ts hadm.1.1]
    exact List.nodup_cons.mpr ⟨hout, hfull⟩
  exact (List.nodup_map_iff hexAWPos_injective).mp hmapped



theorem hexCSBrickDirections_vertices_nodup
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (ts : List ℤ) (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    (ons_pathVertices (hexCSBrickDirections 1 ts)).Nodup := by
  have hc := hexCSCoordPath_start_nodup e ts he hne hadm
  have hinj : Function.Injective (fun q : HexAWCoord =>
      hexBrickPos q - hexBrickPos hexCSOutsideStartCoord) := by
    intro c d hcd
    apply hexBrickPos_injective
    rw [Prod.ext_iff] at hcd ⊢
    constructor <;>
      simp only [Prod.fst_sub, Prod.snd_sub] at hcd ⊢ <;> omega
  have hmapped := hc.map hinj
  rw [hexCSCoordPath_brick hexCSOutsideStartCoord 1 ts
    hexCSHeadingFits_start hadm.1.1] at hmapped
  exact hmapped



theorem hexCSCoordPath_mem_cases
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (ts : List ℤ) (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge))
    (q : HexAWCoord)
    (hq : q ∈ hexCSCoordPath hexCSOutsideStartCoord
      (hexCSHeadingFin 1) ts) :
    q = hexCSOutsideStartCoord ∨ q ∈ hexCSVertexSet T L ∨
      q = hexAWNeighbor e.vtx.1 e.edge := by
  have hpos : hexAWPos q ∈
      (hexCSCoordPath hexCSOutsideStartCoord
        (hexCSHeadingFin 1) ts).map hexAWPos :=
    List.mem_map.mpr ⟨q, hq, rfl⟩
  rw [hexCSCoordPath_start_pos ts hadm.1.1] at hpos
  simp only [List.mem_cons] at hpos
  rcases hpos with hstart | hverts
  · left
    exact hexAWPos_injective hstart
  change hexAWPos q ∈ (ofTurns hexAWStart 1 ts).vertices at hverts
  rw [hexEndpoint_vertices_eq_append_lookahead] at hverts
  simp only [List.mem_append, List.mem_singleton] at hverts
  rcases hverts with hphysical | hlook
  · obtain ⟨c, hc, hpc⟩ :=
      hexCS_endpointVertex_inside ts ⟨hadm.1, hadm.2.1⟩ _ hphysical
    right; left
    have hqc : q = c := hexAWPos_injective hpc
    exact hqc ▸ hc
  · right; right
    have hexit := hexCS_endpoint_boundary_exit e ts he hne hadm
    apply hexAWPos_injective
    calc
      hexAWPos q = hexInfra_midAccum hexAWStart 1 ts +
          halfStep (hexInfra_headAccum 1 ts) := hlook
      _ = hexAWMid e.vtx.1 e.edge +
          halfStep (hexCSCanonicalHeading e) := hexit
      _ = hexAWMid e.vtx.1 e.edge +
          halfStep (hexAWHeading e.vtx.1 e.edge) := by
        rw [hexCSCanonicalHeading_halfStep]
      _ = hexAWPos (hexAWNeighbor e.vtx.1 e.edge) :=
        (hexAWNeighborPos_eq_mid_add e.vtx.1 e.edge).symm


def hexCSBrickRadius (T L : ℕ) : ℕ := 4 * (T + L + 2)

theorem hexCS_inside_brick_bounds
    {T L : ℕ} (c : HexAWCoord) (hc : c ∈ hexCSVertexSet T L) :
    let R : ℤ := hexCSBrickRadius T L
    (-R < (hexBrickPos c - hexBrickPos hexCSOutsideStartCoord).1 ∧
      (hexBrickPos c - hexBrickPos hexCSOutsideStartCoord).1 < R ∧
      -R < (hexBrickPos c - hexBrickPos hexCSOutsideStartCoord).2 ∧
      (hexBrickPos c - hexBrickPos hexCSOutsideStartCoord).2 < R) := by
  rw [hexCS_mem_vertexSet_iff] at hc
  rcases c with ⟨i, j, color⟩
  cases color <;>
    simp only [hexCSInStrip, hexAWBookRe2, hexAWDepth,
      hexAWLong] at hc
  all_goals
    simp [hexCSBrickRadius, hexBrickPos, hexCSOutsideStartCoord]
    omega






theorem hexCS_periodicCoord_injective_of_slab
    (l : List (Fin 4)) [NeZero l.length] (dx dy : ℤ)
    (hdisp : ons_pathDisplacement l = (dx, dy))
    (hdx : 0 < dx)
    (hnodup : (ons_pathVertices l).dropLast.Nodup)
    (hx : ∀ z ∈ (ons_pathVertices l).dropLast,
      0 ≤ z.1 ∧ z.1 < dx) :
    Function.Injective
      (ons_periodStateCoord (fun i : Fin l.length => l.get i)) := by
  let d : Fin l.length → Fin 4 := fun i => l.get i
  have hverts : (ons_pathVertices l).dropLast =
      List.ofFn (StatMech.Onsager.BaseCase.pos d) :=
    ons_pathVertices_dropLast_eq_ofFn_pos l
  intro a b hab
  rcases a with ⟨ra, ia⟩
  rcases b with ⟨rb, ib⟩
  have hpaMem : StatMech.Onsager.BaseCase.pos d ia ∈
      (ons_pathVertices l).dropLast := by
    rw [hverts, List.mem_ofFn]
    exact ⟨ia, rfl⟩
  have hpbMem : StatMech.Onsager.BaseCase.pos d ib ∈
      (ons_pathVertices l).dropLast := by
    rw [hverts, List.mem_ofFn]
    exact ⟨ib, rfl⟩
  have hxa := hx _ hpaMem
  have hxb := hx _ hpbMem
  have hfirst := congrArg Prod.fst hab
  have hperiodDisp : ons_pathDisplacement (List.ofFn d) = (dx, dy) := by
    rw [List.ofFn_get]
    exact hdisp
  change StatMech.Onsager.BaseCase.pos d ia +
      ra • ons_pathDisplacement (List.ofFn d) =
    StatMech.Onsager.BaseCase.pos d ib +
      rb • ons_pathDisplacement (List.ofFn d) at hab
  have hfirst' := congrArg Prod.fst hab
  rw [hperiodDisp] at hfirst'
  simp only [Prod.fst_add, Prod.smul_mk, nsmul_eq_mul] at hfirst'
  have hra : ra = rb := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (rb : ℤ) * dx - (ra : ℤ) * dx ≥ dx := by
        have : (ra : ℤ) + 1 ≤ rb := by exact_mod_cast hlt
        nlinarith
      nlinarith [hfirst']
    · have : (ra : ℤ) * dx - (rb : ℤ) * dx ≥ dx := by
        have : (rb : ℤ) + 1 ≤ ra := by exact_mod_cast hgt
        nlinarith
      nlinarith [hfirst']
  subst rb
  have hpos : StatMech.Onsager.BaseCase.pos d ia =
      StatMech.Onsager.BaseCase.pos d ib := by
    simpa [ons_periodStateCoord] using hab
  have hget : ia = ib := by
    have hinj : Function.Injective (StatMech.Onsager.BaseCase.pos d) :=
      ons_pos_get_injective_of_vertices_dropLast_nodup l hnodup
    exact hinj hpos
  subst ib
  rfl



theorem hexCS_cyclicTurnSum_eq_zero_of_slab
    (l : List (Fin 4)) [NeZero l.length] (dx dy : ℤ)
    (hdisp : ons_pathDisplacement l = (dx, dy))
    (hdx : 0 < dx)
    (hnodup : (ons_pathVertices l).dropLast.Nodup)
    (hx : ∀ z ∈ (ons_pathVertices l).dropLast,
      0 ≤ z.1 ∧ z.1 < dx) :
    ons_cyclicTurnSum l = 0 := by
  let d : Fin l.length → Fin 4 := fun i => l.get i
  have hinj : Function.Injective (ons_periodStateCoord d) :=
    hexCS_periodicCoord_injective_of_slab l dx dy hdisp hdx hnodup hx
  have hnonzero :
      (ons_pathDisplacement (List.ofFn d)).1 ≠ 0 ∨
        (ons_pathDisplacement (List.ofFn d)).2 ≠ 0 := by
    left
    rw [List.ofFn_get, hdisp]
    omega
  have hturn := ons_periodicSimple_cyclicTurnSum_eq_zero_of_nonzero
    d hinj hnonzero
  simpa [d] using hturn




theorem hexCS_periodicCoord_injective_of_negative_slab
    (l : List (Fin 4)) [NeZero l.length] (dx dy : ℤ)
    (hdisp : ons_pathDisplacement l = (dx, dy))
    (hdx : dx < 0)
    (hnodup : (ons_pathVertices l).dropLast.Nodup)
    (hx : ∀ z ∈ (ons_pathVertices l).dropLast,
      dx < z.1 ∧ z.1 ≤ 0) :
    Function.Injective
      (ons_periodStateCoord (fun i : Fin l.length => l.get i)) := by
  let d : Fin l.length → Fin 4 := fun i => l.get i
  have hverts : (ons_pathVertices l).dropLast =
      List.ofFn (StatMech.Onsager.BaseCase.pos d) :=
    ons_pathVertices_dropLast_eq_ofFn_pos l
  intro a b hab
  rcases a with ⟨ra, ia⟩
  rcases b with ⟨rb, ib⟩
  have hpaMem : StatMech.Onsager.BaseCase.pos d ia ∈
      (ons_pathVertices l).dropLast := by
    rw [hverts, List.mem_ofFn]
    exact ⟨ia, rfl⟩
  have hpbMem : StatMech.Onsager.BaseCase.pos d ib ∈
      (ons_pathVertices l).dropLast := by
    rw [hverts, List.mem_ofFn]
    exact ⟨ib, rfl⟩
  have hxa := hx _ hpaMem
  have hxb := hx _ hpbMem
  have hperiodDisp : ons_pathDisplacement (List.ofFn d) = (dx, dy) := by
    rw [List.ofFn_get]
    exact hdisp
  change StatMech.Onsager.BaseCase.pos d ia +
      ra • ons_pathDisplacement (List.ofFn d) =
    StatMech.Onsager.BaseCase.pos d ib +
      rb • ons_pathDisplacement (List.ofFn d) at hab
  have hfirst := congrArg Prod.fst hab
  rw [hperiodDisp] at hfirst
  simp only [Prod.fst_add, Prod.smul_mk, nsmul_eq_mul] at hfirst
  have hra : ra = rb := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hstep : (ra : ℤ) * dx - (rb : ℤ) * dx ≥ -dx := by
        have hr : (ra : ℤ) + 1 ≤ rb := by exact_mod_cast hlt
        nlinarith
      nlinarith [hfirst]
    · have hstep : (rb : ℤ) * dx - (ra : ℤ) * dx ≥ -dx := by
        have hr : (rb : ℤ) + 1 ≤ ra := by exact_mod_cast hgt
        nlinarith
      nlinarith [hfirst]
  subst rb
  have hpos : StatMech.Onsager.BaseCase.pos d ia =
      StatMech.Onsager.BaseCase.pos d ib := by
    simpa [ons_periodStateCoord] using hab
  have hinj : Function.Injective (StatMech.Onsager.BaseCase.pos d) :=
    ons_pos_get_injective_of_vertices_dropLast_nodup l hnodup
  have hib : ia = ib := hinj hpos
  subst ib
  rfl


theorem hexCS_cyclicTurnSum_eq_zero_of_negative_slab
    (l : List (Fin 4)) [NeZero l.length] (dx dy : ℤ)
    (hdisp : ons_pathDisplacement l = (dx, dy))
    (hdx : dx < 0)
    (hnodup : (ons_pathVertices l).dropLast.Nodup)
    (hx : ∀ z ∈ (ons_pathVertices l).dropLast,
      dx < z.1 ∧ z.1 ≤ 0) :
    ons_cyclicTurnSum l = 0 := by
  let d : Fin l.length → Fin 4 := fun i => l.get i
  have hinj : Function.Injective (ons_periodStateCoord d) :=
    hexCS_periodicCoord_injective_of_negative_slab
      l dx dy hdisp hdx hnodup hx
  have hnonzero :
      (ons_pathDisplacement (List.ofFn d)).1 ≠ 0 ∨
        (ons_pathDisplacement (List.ofFn d)).2 ≠ 0 := by
    left
    rw [List.ofFn_get, hdisp]
    omega
  have hturn := ons_periodicSimple_cyclicTurnSum_eq_zero_of_nonzero
    d hinj hnonzero
  simpa [d] using hturn





theorem hexCSCoordPath_eq_prefixCoords
    (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    hexCSCoordPath hexCSOutsideStartCoord (hexCSHeadingFin 1) ts =
      hexCSOutsideStartCoord ::
        List.ofFn (fun k : Fin (ts.length + 1) =>
          hexEndpointPrefixCoord ts hlegal k.val) := by
  apply hexAWPos_injective.list_map
  rw [hexCSCoordPath_start_pos ts hlegal]
  congr 1
  apply List.ext_getElem
  · simp [length_verticesAux]
  · intro k hk hk'
    have hkle : k ≤ ts.length := by
      rw [length_verticesAux] at hk
      omega
    have hget := hexJordan_verticesAux_getElem?_eq
      hexAWStart 1 ts k hkle
    rw [List.getElem?_eq_getElem hk, Option.some.injEq] at hget
    rw [List.getElem_map, List.getElem_ofFn]
    have hp := hexEndpointPrefixCoord_pos ts hlegal k
    unfold hexJordan_vertexPos at hp
    exact hget.trans hp



theorem hexCS_finalPrefixCoord_eq_outside
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    hexEndpointPrefixCoord ts hadm.1.1 ts.length =
      hexAWNeighbor e.vtx.1 e.edge := by
  apply hexAWPos_injective
  rw [← hexEndpointPrefixCoord_pos ts hadm.1.1 ts.length]
  have hx := hexCS_endpoint_boundary_exit e ts he hne hadm
  calc
    hexJordan_vertexPos hexAWStart 1 ts ts.length =
        hexInfra_midAccum hexAWStart 1 ts +
          halfStep (hexInfra_headAccum 1 ts) := by
      simp [hexJordan_vertexPos]
    _ = hexAWMid e.vtx.1 e.edge +
          halfStep (hexCSCanonicalHeading e) := hx
    _ = hexAWPos (hexAWNeighbor e.vtx.1 e.edge) := by
      rw [hexCSCanonicalHeading_halfStep]
      exact (hexAWNeighborPos_eq_mid_add e.vtx.1 e.edge).symm


theorem hexCSOutsideStart_ne_endpointOutside
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT) :
    hexCSOutsideStartCoord ≠ hexAWNeighbor e.vtx.1 e.edge := by
  intro hout
  have hmidMem : hexAWMid e.vtx.1 e.edge ∈ hexCSMids T L := by
    rw [hexCSMids, Finset.mem_biUnion]
    refine ⟨e.vtx, Finset.mem_univ _, ?_⟩
    rw [Finset.mem_image]
    exact ⟨e.edge, Finset.mem_univ _, rfl⟩
  have houtsideMid :
      hexAWMid hexCSOutsideStartCoord e.edge ∈ hexCSMids T L := by
    rw [hout, hexAWMid_neighbor]
    exact hmidMem
  have hedge : e.edge = 0 :=
    (hexCSOutsideStart_mid_mem_iff T L hT e.edge).mp houtsideMid
  apply hne
  apply hexCSBoundaryIncidence_eq_start_of_mid e
  calc
    hexAWMid e.vtx.1 e.edge =
        hexAWMid (hexAWNeighbor e.vtx.1 e.edge) e.edge :=
      (hexAWMid_neighbor e.vtx.1 e.edge).symm
    _ = hexAWMid hexCSOutsideStartCoord 0 := by rw [← hout, hedge]
    _ = hexAWStart := hexCSOutsideStart_mid_zero


theorem hexCSCoordPath_nodup
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    (hexCSCoordPath hexCSOutsideStartCoord
      (hexCSHeadingFin 1) ts).Nodup := by
  rw [hexCSCoordPath_eq_prefixCoords ts hadm.1.1,
    List.nodup_cons]
  constructor
  · rw [List.mem_ofFn]
    rintro ⟨k, hk⟩
    by_cases hlast : k.val = ts.length
    · have hfinal := hexCS_finalPrefixCoord_eq_outside e ts he hne hadm
      rw [hlast, hfinal] at hk
      exact hexCSOutsideStart_ne_endpointOutside e he hne hk.symm
    · have hklt : k.val < ts.length := by omega
      have hmem := hexCS_prefixCoord_mem ts ⟨hadm.1, hadm.2.1⟩
        k.val hklt
      rw [hk] at hmem
      have hout : hexCSOutsideStartCoord ∉ hexCSVertexSet T L := by
        rw [hexCS_mem_vertexSet_iff]
        simp [hexCSOutsideStartCoord, hexCSInStrip,
          hexAWBookRe2, hexAWDepth, hexAWLong]
      exact hout hmem
  · rw [List.nodup_ofFn]
    intro i j hij
    change hexEndpointPrefixCoord ts hadm.1.1 i.val =
      hexEndpointPrefixCoord ts hadm.1.1 j.val at hij
    by_cases hilast : i.val = ts.length
    · by_cases hjlast : j.val = ts.length
      · apply Fin.ext
        omega
      · have hjlt : j.val < ts.length := by omega
        have hfinal := hexCS_finalPrefixCoord_eq_outside e ts he hne hadm
        have hjmem := hexCS_prefixCoord_mem ts ⟨hadm.1, hadm.2.1⟩
          j.val hjlt
        rw [hilast, hfinal] at hij
        rw [← hij] at hjmem
        exact (hexCSOutsideBoundary_not_mem e he hjmem).elim
    · by_cases hjlast : j.val = ts.length
      · have hilt : i.val < ts.length := by omega
        have hfinal := hexCS_finalPrefixCoord_eq_outside e ts he hne hadm
        have himem := hexCS_prefixCoord_mem ts ⟨hadm.1, hadm.2.1⟩
          i.val hilt
        rw [hjlast, hfinal] at hij
        rw [hij] at himem
        exact (hexCSOutsideBoundary_not_mem e he himem).elim
      · have hilt : i.val < ts.length := by omega
        have hjlt : j.val < ts.length := by omega
        apply Fin.ext
        by_contra hval
        apply (hexEndpoint_vertexPos_ne_of_saw ts hadm.1.2
          i.val j.val hilt hjlt hval)
        rw [hexEndpointPrefixCoord_pos ts hadm.1.1 i.val,
          hexEndpointPrefixCoord_pos ts hadm.1.1 j.val]
        exact congrArg hexAWPos hij




def hexCSEndDelta {T L : ℕ} (e : HexCSIncidence T L) : ℤ × ℤ :=
  hexBrickPos (hexAWNeighbor e.vtx.1 e.edge) -
    hexBrickPos hexCSOutsideStartCoord



theorem hexCSBrickDirections_displacement
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    ons_pathDisplacement (hexCSBrickDirections 1 ts) =
      hexCSEndDelta e := by
  have hcoordlast :
      (hexCSCoordPath hexCSOutsideStartCoord
        (hexCSHeadingFin 1) ts).getLast? =
        some (hexAWNeighbor e.vtx.1 e.edge) := by
    rw [hexCSCoordPath_eq_prefixCoords ts hadm.1.1]
    rw [List.getLast?_eq_getLast (by simp)]
    rw [List.getLast_cons (by simp), List.getLast_ofFn (by simp)]
    apply congrArg some
    convert hexCS_finalPrefixCoord_eq_outside e ts he hne hadm using 1 <;>
      simp
  have hb := hexCSCoordPath_brick hexCSOutsideStartCoord 1 ts
    hexCSHeadingFits_start hadm.1.1
  have hg := congrArg List.getLast? hb
  simp only [List.getLast?_map, hcoordlast,
    Option.map_some, ons_pathVertices_getLast] at hg
  exact (Option.some.inj hg).symm



theorem hexCS_inside_brick_depth_pos
    {T L : ℕ} (c : HexAWCoord) (hc : c ∈ hexCSVertexSet T L) :
    0 < (hexBrickPos c - hexBrickPos hexCSOutsideStartCoord).2 -
      (hexBrickPos c - hexBrickPos hexCSOutsideStartCoord).1 := by
  rw [hexCS_mem_vertexSet_iff] at hc
  rcases c with ⟨i, j, color⟩
  cases color <;>
    simp only [hexCSInStrip, hexAWBookRe2, hexAWDepth,
      hexAWLong] at hc
  all_goals
    simp [hexBrickPos, hexCSOutsideStartCoord]
    omega


theorem hexCSEndDelta_bounds
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L) :
    let R : ℤ := hexCSBrickRadius T L
    (-R < (hexCSEndDelta e).1 ∧
      (hexCSEndDelta e).1 < R ∧
      -R < (hexCSEndDelta e).2 ∧
      (hexCSEndDelta e).2 < R) := by
  have hc := (hexCS_mem_vertexSet_iff T L e.vtx.1).1 e.vtx.2
  have hb := hexCS_boundary_classification e he
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  cases color <;> fin_cases edge <;>
    simp [hexCSEndDelta, hexBrickPos, hexCSOutsideStartCoord,
      hexAWNeighbor, hexCSBrickRadius, hexCSInStrip, hexAWBookRe2,
      hexAWDepth, hexAWLong, hexAWTrans] at hc hb ⊢ <;> omega



theorem hexCSBrickDirections_dropLast_mem_cases
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge))
    (z : ℤ × ℤ)
    (hz : z ∈ (ons_pathVertices
      (hexCSBrickDirections 1 ts)).dropLast) :
    z = 0 ∨ ∃ c : HexAWCoord, c ∈ hexCSVertexSet T L ∧
      z = hexBrickPos c - hexBrickPos hexCSOutsideStartCoord := by
  have hfull := hexCSBrickDirections_vertices_nodup e ts he hne hadm
  have hend : hexCSEndDelta e ∉
      (ons_pathVertices (hexCSBrickDirections 1 ts)).dropLast := by
    rw [← hexCSBrickDirections_displacement e ts he hne hadm]
    exact ons_pathDisplacement_not_mem_dropLast_of_vertices_nodup _ hfull
  have hzfull : z ∈ ons_pathVertices (hexCSBrickDirections 1 ts) :=
    List.mem_of_mem_dropLast hz
  have hb := hexCSCoordPath_brick hexCSOutsideStartCoord 1 ts
    hexCSHeadingFits_start hadm.1.1
  rw [← hb] at hzfull
  obtain ⟨q, hq, hqz⟩ := List.mem_map.mp hzfull
  rcases hexCSCoordPath_mem_cases e ts he hne hadm q hq with
      hstart | hin | hout
  · left
    rw [← hqz, hstart]
    exact sub_self _
  · right
    exact ⟨q, hin, hqz.symm⟩
  · exfalso
    apply hend
    have hze : z = hexCSEndDelta e := by
      rw [← hqz, hout]
      rfl
    rw [← hze]
    exact hz



def hexCSSourceBelow (R : ℕ) : List (Fin 4) :=
  List.replicate (2 * R) 0 ++
    List.replicate R 1 ++ List.replicate R 2

def hexCSSourceAbove (R : ℕ) : List (Fin 4) :=
  List.replicate (2 * R) 0 ++
    List.replicate R 3 ++ List.replicate R 2

def hexCSEastTail (R : ℕ) (dx : ℤ) : List (Fin 4) :=
  List.replicate ((R : ℤ) + 1 - dx).toNat 0

def hexCSWestNorthEastTail (R : ℕ) (dx dy : ℤ) : List (Fin 4) :=
  List.replicate (dx + (R : ℤ)).toNat 2 ++
    List.replicate ((R : ℤ) - dy).toNat 1 ++
    List.replicate (2 * R + 1) 0

def hexCSSouthEastTail (R : ℕ) (dx dy : ℤ) : List (Fin 4) :=
  List.replicate (dy + R).toNat 3 ++
    List.replicate ((R : ℤ) + 1 - dx).toNat 0

theorem hexCSSourceBelow_displacement (R : ℕ) :
    ons_pathDisplacement (hexCSSourceBelow R) = ((R : ℤ), (R : ℤ)) := by
  ext <;> simp [hexCSSourceBelow, ons_pathDisplacement_append,
    ons_pathDisplacement_replicate, StatMech.Onsager.BaseCase.stepOf,
    Prod.smul_mk] <;> omega

theorem hexCSSourceAbove_displacement (R : ℕ) :
    ons_pathDisplacement (hexCSSourceAbove R) = ((R : ℤ), -(R : ℤ)) := by
  ext <;> simp [hexCSSourceAbove, ons_pathDisplacement_append,
    ons_pathDisplacement_replicate, StatMech.Onsager.BaseCase.stepOf,
    Prod.smul_mk] <;> omega

theorem hexCSEastTail_displacement (R : ℕ) (dx : ℤ)
    (h : dx ≤ R) :
    ons_pathDisplacement (hexCSEastTail R dx) =
      ((R : ℤ) + 1 - dx, 0) := by
  simp [hexCSEastTail, ons_pathDisplacement_replicate,
    StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk,
    Int.toNat_of_nonneg (by omega : 0 ≤ (R : ℤ) + 1 - dx)]

theorem hexCSSouthEastTail_displacement (R : ℕ) (dx dy : ℤ)
    (hx : dx ≤ R) (hy : -(R : ℤ) ≤ dy) :
    ons_pathDisplacement (hexCSSouthEastTail R dx dy) =
      ((R : ℤ) + 1 - dx, -((R : ℤ) + dy)) := by
  ext <;> simp [hexCSSouthEastTail, ons_pathDisplacement_append,
    ons_pathDisplacement_replicate, StatMech.Onsager.BaseCase.stepOf,
    Prod.smul_mk,
    Int.toNat_of_nonneg (by omega : 0 ≤ dy + R),
    Int.toNat_of_nonneg (by omega : 0 ≤ (R : ℤ) + 1 - dx)] <;> omega

theorem hexCSWestNorthEastTail_displacement
    (R : ℕ) (dx dy : ℤ)
    (hx : -(R : ℤ) ≤ dx) (hy : dy ≤ R) :
    ons_pathDisplacement (hexCSWestNorthEastTail R dx dy) =
      ((R : ℤ) + 1 - dx, (R : ℤ) - dy) := by
  ext <;> simp [hexCSWestNorthEastTail, ons_pathDisplacement_append,
    ons_pathDisplacement_replicate, StatMech.Onsager.BaseCase.stepOf,
    Prod.smul_mk,
    Int.toNat_of_nonneg (by omega : 0 ≤ dx + R),
    Int.toNat_of_nonneg (by omega : 0 ≤ (R : ℤ) - dy)] <;> omega

theorem hexCS_openTurn_three_replicates
    (a b c : Fin 4) (na nb nc : ℕ) :
    ons_openTurnSum (List.replicate (na + 1) a ++
      List.replicate (nb + 1) b ++ List.replicate (nc + 1) c) =
      ons_turnPow a b + ons_turnPow b c := by
  rw [List.append_assoc,
    ons_openTurnSum_append (List.replicate (na + 1) a)
      (List.replicate (nb + 1) b ++ List.replicate (nc + 1) c)
      (by simp) (by simp),
    ons_openTurnSum_append (List.replicate (nb + 1) b)
      (List.replicate (nc + 1) c) (by simp) (by simp)]
  simp [ons_openTurnSum_replicate]

theorem hexCS_openTurn_two_replicates
    (a b : Fin 4) (na nb : ℕ) :
    ons_openTurnSum (List.replicate (na + 1) a ++
      List.replicate (nb + 1) b) = ons_turnPow a b := by
  rw [ons_openTurnSum_append _ _ (by simp) (by simp)]
  simp [ons_openTurnSum_replicate]

theorem hexCSSourceBelow_openTurn (R : ℕ) (hR : 0 < R) :
    ons_openTurnSum (hexCSSourceBelow R) = 2 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : R ≠ 0)
  have h := hexCS_openTurn_three_replicates 0 1 2 (2 * r + 1) r r
  norm_num [hexCSSourceBelow, ons_turnPow] at h ⊢
  simpa [show 2 * (r + 1) = 2 * r + 2 by omega] using h

theorem hexCSSourceAbove_openTurn (R : ℕ) (hR : 0 < R) :
    ons_openTurnSum (hexCSSourceAbove R) = -2 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : R ≠ 0)
  have h := hexCS_openTurn_three_replicates 0 3 2 (2 * r + 1) r r
  norm_num [hexCSSourceAbove, ons_turnPow] at h ⊢
  simpa [show 2 * (r + 1) = 2 * r + 2 by omega] using h

theorem hexCSEastTail_openTurn (R : ℕ) (dx : ℤ) :
    ons_openTurnSum (hexCSEastTail R dx) = 0 := by
  exact ons_openTurnSum_replicate _ _

theorem hexCSWestNorthEastTail_openTurn
    (R : ℕ) (dx dy : ℤ)
    (hW : 0 < dx + R) (hN : 0 < (R : ℤ) - dy) :
    ons_openTurnSum (hexCSWestNorthEastTail R dx dy) = -2 := by
  obtain ⟨w, hw⟩ : ∃ w, (dx + R).toNat = w + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    intro hzero
    have hz := Int.toNat_eq_zero.mp hzero
    omega
  obtain ⟨n, hn⟩ : ∃ n, ((R : ℤ) - dy).toNat = n + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    intro hzero
    have hz := Int.toNat_eq_zero.mp hzero
    omega
  obtain ⟨r, hr⟩ : ∃ r : ℕ, 2 * R + 1 = r + 1 := by
    exact ⟨2 * R, rfl⟩
  have h := hexCS_openTurn_three_replicates 2 1 0 w n r
  norm_num [ons_turnPow] at h ⊢
  simpa [hexCSWestNorthEastTail, hw, hn, hr] using h

theorem hexCSSouthEastTail_openTurn
    (R : ℕ) (dx dy : ℤ)
    (hS : 0 < dy + R) (hE : 0 < (R : ℤ) - dx) :
    ons_openTurnSum (hexCSSouthEastTail R dx dy) = 1 := by
  obtain ⟨s, hs⟩ : ∃ s, (dy + R).toNat = s + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    intro hzero
    have hz := Int.toNat_eq_zero.mp hzero
    omega
  obtain ⟨r, hr⟩ : ∃ r, ((R : ℤ) + 1 - dx).toNat = r + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    intro hzero
    have hz := Int.toNat_eq_zero.mp hzero
    omega
  have h := hexCS_openTurn_two_replicates 3 0 s r
  norm_num [ons_turnPow] at h ⊢
  simpa [hexCSSouthEastTail, hs, hr] using h

theorem hexCSSourceBelow_vertices_dropLast_nodup (R : ℕ) :
    (ons_pathVertices (hexCSSourceBelow R)).dropLast.Nodup := by
  rw [hexCSSourceBelow, List.append_assoc,
    ons_pathVertices_append_dropLast,
    ons_pathVertices_append_dropLast]
  simp only [ons_pathVertices_replicate_dropLast]
  simp only [List.map_append, List.map_map, Function.comp_apply]
  simp [ons_pathDisplacement_replicate,
    StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk,
    List.nodup_append]
  repeat' apply And.intro
  all_goals
    first
    | apply List.Nodup.map (by
        intro a b hab
        have hx := congrArg (fun z : ℤ × ℤ => z.1) hab
        have hy := congrArg (fun z : ℤ × ℤ => z.2) hab
        simp [Function.comp_def] at hx hy
        omega)
      exact List.nodup_range
    | omega

theorem hexCSSourceAbove_vertices_dropLast_nodup (R : ℕ) :
    (ons_pathVertices (hexCSSourceAbove R)).dropLast.Nodup := by
  rw [hexCSSourceAbove, List.append_assoc,
    ons_pathVertices_append_dropLast,
    ons_pathVertices_append_dropLast]
  simp only [ons_pathVertices_replicate_dropLast]
  simp only [List.map_append, List.map_map, Function.comp_apply]
  simp [ons_pathDisplacement_replicate,
    StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk,
    List.nodup_append]
  repeat' apply And.intro
  all_goals
    first
    | apply List.Nodup.map (by
        intro a b hab
        have hx := congrArg (fun z : ℤ × ℤ => z.1) hab
        have hy := congrArg (fun z : ℤ × ℤ => z.2) hab
        simp [Function.comp_def] at hx hy
        omega)
      exact List.nodup_range
    | omega

theorem hexCSSourceBelow_vertex_cases
    (R : ℕ) (z : ℤ × ℤ)
    (hz : z ∈ (ons_pathVertices (hexCSSourceBelow R)).dropLast) :
    (∃ k : ℕ, k < 2 * R ∧ z = ((k : ℤ), 0)) ∨
      (∃ k : ℕ, k < R ∧
        z = (2 * (R : ℤ), (k : ℤ))) ∨
      (∃ k : ℕ, k < R ∧
        z = (2 * (R : ℤ) - (k : ℤ), (R : ℤ))) := by
  rw [hexCSSourceBelow, List.append_assoc,
    ons_pathVertices_append_dropLast,
    ons_pathVertices_append_dropLast] at hz
  simp only [ons_pathVertices_replicate_dropLast] at hz
  simp [ons_pathDisplacement_replicate,
    StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk] at hz ⊢
  rcases hz with hz | hz | hz
  · left
    simpa only [eq_comm] using hz
  · right; left
    simpa only [eq_comm] using hz
  · right; right
    obtain ⟨k, hk, rfl⟩ := hz
    exact ⟨k, hk, by ext <;> simp <;> ring⟩

theorem hexCSSourceAbove_vertex_cases
    (R : ℕ) (z : ℤ × ℤ)
    (hz : z ∈ (ons_pathVertices (hexCSSourceAbove R)).dropLast) :
    (∃ k : ℕ, k < 2 * R ∧ z = ((k : ℤ), 0)) ∨
      (∃ k : ℕ, k < R ∧
        z = (2 * (R : ℤ), -(k : ℤ))) ∨
      (∃ k : ℕ, k < R ∧
        z = (2 * (R : ℤ) - (k : ℤ), -(R : ℤ))) := by
  rw [hexCSSourceAbove, List.append_assoc,
    ons_pathVertices_append_dropLast,
    ons_pathVertices_append_dropLast] at hz
  simp only [ons_pathVertices_replicate_dropLast] at hz
  simp [ons_pathDisplacement_replicate,
    StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk] at hz ⊢
  rcases hz with hz | hz | hz
  · left
    simpa only [eq_comm] using hz
  · right; left
    obtain ⟨k, hk, hkz⟩ := hz
    exact ⟨k, hk, hkz.symm⟩
  · right; right
    obtain ⟨k, hk, hkz⟩ := hz
    exact ⟨k, hk, by rw [← hkz]; ext <;> simp <;> ring⟩

theorem hexCSEastTail_vertices_dropLast_nodup (R : ℕ) (dx : ℤ) :
    (ons_pathVertices (hexCSEastTail R dx)).dropLast.Nodup := by
  rw [hexCSEastTail, ons_pathVertices_replicate_dropLast]
  apply List.Nodup.map (by
    intro a b hab
    have hx := congrArg (fun z : ℤ × ℤ => z.1) hab
    simp [StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk] at hx
    omega)
  exact List.nodup_range

theorem hexCSWestNorthEastTail_vertices_dropLast_nodup
    (R : ℕ) (dx dy : ℤ)
    (hW : 0 < dx + R) (hN : 0 < (R : ℤ) - dy) :
    (ons_pathVertices
      (hexCSWestNorthEastTail R dx dy)).dropLast.Nodup := by
  rw [hexCSWestNorthEastTail, List.append_assoc,
    ons_pathVertices_append_dropLast,
    ons_pathVertices_append_dropLast]
  simp only [ons_pathVertices_replicate_dropLast]
  simp only [List.map_append, List.map_map, Function.comp_apply]
  simp [ons_pathDisplacement_replicate,
    StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk,
    List.nodup_append,
    Int.toNat_of_nonneg (by omega : 0 ≤ dx + R),
    Int.toNat_of_nonneg (by omega : 0 ≤ (R : ℤ) - dy)]
  repeat' apply And.intro
  all_goals
    first
    | apply List.Nodup.map (by
        intro a b hab
        have hx := congrArg (fun z : ℤ × ℤ => z.1) hab
        have hy := congrArg (fun z : ℤ × ℤ => z.2) hab
        simp [Function.comp_def] at hx hy
        omega)
      exact List.nodup_range
    | omega

theorem hexCSSouthEastTail_vertices_dropLast_nodup
    (R : ℕ) (dx dy : ℤ)
    (hS : 0 < dy + R) :
    (ons_pathVertices
      (hexCSSouthEastTail R dx dy)).dropLast.Nodup := by
  rw [hexCSSouthEastTail, ons_pathVertices_append_dropLast]
  simp only [ons_pathVertices_replicate_dropLast]
  simp only [List.map_map, Function.comp_apply]
  simp [ons_pathDisplacement_replicate,
    StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk,
    List.nodup_append,
    Int.toNat_of_nonneg (by omega : 0 ≤ dy + R)]
  repeat' apply And.intro
  all_goals
    first
    | apply List.Nodup.map (by
        intro a b hab
        have hx := congrArg (fun z : ℤ × ℤ => z.1) hab
        have hy := congrArg (fun z : ℤ × ℤ => z.2) hab
        simp [Function.comp_def] at hx hy
        omega)
      exact List.nodup_range
    | omega

theorem hexCSEastTail_endpoint_vertex_cases
    (R : ℕ) (dx dy : ℤ) (z : ℤ × ℤ)
    (hz : z ∈ (ons_pathVertices (hexCSEastTail R dx)).dropLast) :
    ∃ k : ℕ, k < ((R : ℤ) + 1 - dx).toNat ∧
      (dx, dy) + z = (dx + k, dy) := by
  obtain ⟨k, hk, hkz⟩ :=
    (ons_mem_pathVertices_replicate_dropLast_iff
      ((R : ℤ) + 1 - dx).toNat 0 z).mp (by
        simpa [hexCSEastTail] using hz)
  refine ⟨k, hk, ?_⟩
  rw [hkz]
  ext <;>
    simp [StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk] <;> ring

theorem hexCSWestNorthEastTail_endpoint_vertex_cases
    (R : ℕ) (dx dy : ℤ)
    (hx : 0 ≤ dx + R) (hy : 0 ≤ (R : ℤ) - dy)
    (z : ℤ × ℤ)
    (hz : z ∈ (ons_pathVertices
      (hexCSWestNorthEastTail R dx dy)).dropLast) :
    (∃ k : ℕ, k < (dx + R).toNat ∧
        (dx, dy) + z = (dx - k, dy)) ∨
      (∃ k : ℕ, k < ((R : ℤ) - dy).toNat ∧
        (dx, dy) + z = (-(R : ℤ), dy + k)) ∨
      (∃ k : ℕ, k < 2 * R + 1 ∧
        (dx, dy) + z = (-(R : ℤ) + k, (R : ℤ))) := by
  let A := List.replicate (dx + R).toNat (2 : Fin 4)
  let B := List.replicate ((R : ℤ) - dy).toNat (1 : Fin 4)
  let C := List.replicate (2 * R + 1) (0 : Fin 4)
  have hshape : hexCSWestNorthEastTail R dx dy = A ++ (B ++ C) := by
    simp [hexCSWestNorthEastTail, A, B, C, List.append_assoc]
  rw [hshape] at hz
  rcases (ons_mem_pathVertices_append_dropLast_iff
      A (B ++ C) z).mp hz with hwest | ⟨z₁, hz₁, ez₁⟩
  · left
    obtain ⟨k, hk, hkz⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff
        (dx + R).toNat 2 z).mp (by simpa [A] using hwest)
    refine ⟨k, hk, ?_⟩
    rw [hkz]
    ext <;>
      simp [StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk] <;> ring
  rcases (ons_mem_pathVertices_append_dropLast_iff
      B C z₁).mp hz₁ with hnorth | ⟨z₂, hz₂, ez₂⟩
  · right; left
    obtain ⟨k, hk, hkz⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff
        ((R : ℤ) - dy).toNat 1 z₁).mp (by simpa [B] using hnorth)
    refine ⟨k, hk, ?_⟩
    rw [ez₁, hkz,
      show ons_pathDisplacement A =
          (dx + R).toNat • StatMech.Onsager.BaseCase.stepOf 2 by
        simp [A, ons_pathDisplacement_replicate]]
    ext <;>
      simp [StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk,
        Int.toNat_of_nonneg hx] <;> ring
  · right; right
    obtain ⟨k, hk, hkz⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff
        (2 * R + 1) 0 z₂).mp (by simpa [C] using hz₂)
    refine ⟨k, hk, ?_⟩
    rw [ez₁, ez₂, hkz,
      show ons_pathDisplacement A =
          (dx + R).toNat • StatMech.Onsager.BaseCase.stepOf 2 by
        simp [A, ons_pathDisplacement_replicate],
      show ons_pathDisplacement B =
          ((R : ℤ) - dy).toNat •
            StatMech.Onsager.BaseCase.stepOf 1 by
        simp [B, ons_pathDisplacement_replicate]]
    ext <;>
      simp [StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk,
        Int.toNat_of_nonneg hx, Int.toNat_of_nonneg hy] <;> ring

theorem hexCSSouthEastTail_endpoint_vertex_cases
    (R : ℕ) (dx dy : ℤ) (hy : 0 ≤ dy + R)
    (z : ℤ × ℤ)
    (hz : z ∈ (ons_pathVertices
      (hexCSSouthEastTail R dx dy)).dropLast) :
    (∃ k : ℕ, k < (dy + R).toNat ∧
        (dx, dy) + z = (dx, dy - k)) ∨
      (∃ k : ℕ, k < ((R : ℤ) + 1 - dx).toNat ∧
        (dx, dy) + z = (dx + k, -(R : ℤ))) := by
  let A := List.replicate (dy + R).toNat (3 : Fin 4)
  let B := List.replicate ((R : ℤ) + 1 - dx).toNat (0 : Fin 4)
  have hshape : hexCSSouthEastTail R dx dy = A ++ B := by
    simp [hexCSSouthEastTail, A, B]
  rw [hshape] at hz
  rcases (ons_mem_pathVertices_append_dropLast_iff
      A B z).mp hz with hsouth | ⟨z₁, hz₁, ez₁⟩
  · left
    obtain ⟨k, hk, hkz⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff
        (dy + R).toNat 3 z).mp (by simpa [A] using hsouth)
    refine ⟨k, hk, ?_⟩
    rw [hkz]
    ext <;>
      simp [StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk] <;> ring
  · right
    obtain ⟨k, hk, hkz⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff
        ((R : ℤ) + 1 - dx).toNat 0 z₁).mp (by simpa [B] using hz₁)
    refine ⟨k, hk, ?_⟩
    rw [ez₁, hkz,
      show ons_pathDisplacement A =
          (dy + R).toNat • StatMech.Onsager.BaseCase.stepOf 3 by
        simp [A, ons_pathDisplacement_replicate]]
    ext <;>
      simp [StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk,
        Int.toNat_of_nonneg hy] <;> ring



theorem hexCSEndDelta_left_sign
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hc : e.vtx.1.color = .black) (hedge : e.edge = 0) :
    (0 ≤ hexAWTrans e.vtx.1 → 0 < (hexCSEndDelta e).2) ∧
      (¬ 0 ≤ hexAWTrans e.vtx.1 →
        (hexCSEndDelta e).2 < 0) := by
  have hb := hexCS_boundary_classification e he
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  cases color <;> fin_cases edge <;>
    simp [hexCSEndDelta, hexBrickPos, hexCSOutsideStartCoord,
      hexAWNeighbor, hexAWTrans, hexAWDepth, hexAWLong] at hc hedge hb ⊢
  constructor <;> intro hs
  · by_contra hstrict
    have hzero : i = 0 ∧ j = 0 := by omega
    apply hne
    rw [HexIncidence.mk.injEq]
    constructor
    · apply Subtype.ext
      simp [hexCSStartIncidence, hexCSOrigin, hexAWOriginCoord,
        hzero.1, hzero.2]
    · rfl
  · omega

theorem hexCSEndDelta_slant_sign
    {T L : ℕ} (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L) :
    (e.vtx.1.color = .white ∧ e.edge = 1 →
        0 < (hexCSEndDelta e).2) ∧
      (e.vtx.1.color = .white ∧ e.edge = 2 →
        (hexCSEndDelta e).2 < 0) := by
  have hc := (hexCS_mem_vertexSet_iff T L e.vtx.1).1 e.vtx.2
  have hb := hexCS_boundary_classification e he
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  cases color <;> fin_cases edge <;>
    simp [hexCSEndDelta, hexBrickPos, hexCSOutsideStartCoord,
      hexAWNeighbor, hexCSInStrip, hexAWBookRe2,
      hexAWDepth, hexAWLong] at hc hb ⊢ <;> omega

theorem hexCSEndDelta_right_zero_height
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hc : e.vtx.1.color = .white) (hedge : e.edge = 0)
    (hy : (hexCSEndDelta e).2 = 0) :
    (hexCSEndDelta e).1 < 0 := by
  have hb := hexCS_boundary_classification e he
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  cases color <;> fin_cases edge <;>
    simp [hexCSEndDelta, hexBrickPos, hexCSOutsideStartCoord,
      hexAWNeighbor, hexAWDepth, hexAWLong] at hc hedge hb hy ⊢ <;>
    omega



theorem hexCSEastRay_not_inside
    {T L : ℕ} (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hside :
      (e.vtx.1.color = .black ∧ e.edge = 0 ∧
        hexAWDepth e.vtx.1 = 0) ∨
      (e.vtx.1.color = .white ∧ e.edge = 1 ∧
        e.vtx.1.i = L))
    (c : HexAWCoord) (hc : c ∈ hexCSVertexSet T L) (k : ℕ) :
    hexBrickPos c - hexBrickPos hexCSOutsideStartCoord ≠
      hexCSEndDelta e + ((k : ℤ), 0) := by
  rw [hexCS_mem_vertexSet_iff] at hc
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  rcases c with ⟨a, b, ccolor⟩
  cases color <;> fin_cases edge <;> cases ccolor <;>
    simp [hexCSEndDelta, hexBrickPos, hexCSOutsideStartCoord,
      hexAWNeighbor, hexAWDepth, hexAWLong, hexCSInStrip,
      hexAWBookRe2] at hside hc ⊢ <;> omega


theorem hexCSWestRay_not_inside
    {T L : ℕ} (e : HexCSIncidence T L)
    (hside : e.vtx.1.color = .white ∧ e.edge = 0 ∧
      hexAWDepth e.vtx.1 = T)
    (c : HexAWCoord) (hc : c ∈ hexCSVertexSet T L) (k : ℕ) :
    hexBrickPos c - hexBrickPos hexCSOutsideStartCoord ≠
      hexCSEndDelta e + (-(k : ℤ), 0) := by
  rw [hexCS_mem_vertexSet_iff] at hc
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  rcases c with ⟨a, b, ccolor⟩
  cases color <;> fin_cases edge <;> cases ccolor <;>
    simp [hexCSEndDelta, hexBrickPos, hexCSOutsideStartCoord,
      hexAWNeighbor, hexAWDepth, hexAWLong, hexCSInStrip,
      hexAWBookRe2] at hside hc ⊢ <;> omega


theorem hexCSSouthRay_not_inside
    {T L : ℕ} (e : HexCSIncidence T L)
    (hside : e.vtx.1.color = .white ∧ e.edge = 2 ∧
      e.vtx.1.j = L)
    (c : HexAWCoord) (hc : c ∈ hexCSVertexSet T L) (k : ℕ) :
    hexBrickPos c - hexBrickPos hexCSOutsideStartCoord ≠
      hexCSEndDelta e + (0, -(k : ℤ)) := by
  rw [hexCS_mem_vertexSet_iff] at hc
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  rcases c with ⟨a, b, ccolor⟩
  cases color <;> fin_cases edge <;> cases ccolor <;>
    simp [hexCSEndDelta, hexBrickPos, hexCSOutsideStartCoord,
      hexAWNeighbor, hexAWDepth, hexAWLong, hexCSInStrip,
      hexAWBookRe2] at hside hc ⊢ <;> omega



theorem hexCS_three_piece_x_slab
    (P C S : List (Fin 4)) (D : ℤ)
    (hP : ∀ p ∈ (ons_pathVertices P).dropLast,
      0 ≤ p.1 ∧ p.1 < D)
    (hC : ∀ c ∈ (ons_pathVertices C).dropLast,
      0 ≤ (ons_pathDisplacement P + c).1 ∧
        (ons_pathDisplacement P + c).1 < D)
    (hS : ∀ s ∈ (ons_pathVertices S).dropLast,
      0 ≤ (ons_pathDisplacement P +
          ons_pathDisplacement C + s).1 ∧
        (ons_pathDisplacement P + ons_pathDisplacement C + s).1 < D) :
    ∀ z ∈ (ons_pathVertices (P ++ C ++ S)).dropLast,
      0 ≤ z.1 ∧ z.1 < D := by
  intro z hz
  rcases (ons_mem_pathVertices_append_dropLast_iff
      (P ++ C) S z).mp hz with hpc | ⟨s, hs, rfl⟩
  · rcases (ons_mem_pathVertices_append_dropLast_iff
        P C z).mp hpc with hp | ⟨c, hc, rfl⟩
    · exact hP z hp
    · exact hC c hc
  · rw [ons_pathDisplacement_append]
    exact hS s hs

theorem hexCSSourceBelow_x_slab (R : ℕ) :
    ∀ p ∈ (ons_pathVertices (hexCSSourceBelow R)).dropLast,
      0 ≤ p.1 ∧ p.1 < (2 * R + 1 : ℕ) := by
  intro p hp
  rcases hexCSSourceBelow_vertex_cases R p hp with
      ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;>
    simp <;> omega

theorem hexCSSourceAbove_x_slab (R : ℕ) :
    ∀ p ∈ (ons_pathVertices (hexCSSourceAbove R)).dropLast,
      0 ≤ p.1 ∧ p.1 < (2 * R + 1 : ℕ) := by
  intro p hp
  rcases hexCSSourceAbove_vertex_cases R p hp with
      ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;>
    simp <;> omega

theorem hexCS_central_x_slab
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    let R := hexCSBrickRadius T L
    ∀ c ∈ (ons_pathVertices
      (hexCSBrickDirections 1 ts)).dropLast,
      0 ≤ (((R : ℤ), 0) + c).1 ∧
        (((R : ℤ), 0) + c).1 < (((2 * R + 1 : ℕ) : ℤ)) := by
  dsimp only
  let R := hexCSBrickRadius T L
  intro c hc
  rcases hexCSBrickDirections_dropLast_mem_cases
      e ts he hne hadm c hc with rfl | ⟨q, hq, rfl⟩
  · simp
    have hR : 0 < (R : ℤ) := by
      dsimp [R, hexCSBrickRadius]
      omega
    omega
  · have hb := hexCS_inside_brick_bounds q hq
    dsimp only at hb
    let qx := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).1
    change (-(R : ℤ) < qx ∧ qx < R ∧
      -(R : ℤ) <
          (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2 ∧
        (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2 < R) at hb
    change 0 ≤ (R : ℤ) + qx ∧
      (R : ℤ) + qx < 2 * R + 1
    omega

theorem hexCSEastTail_x_slab
    (R : ℕ) (dx dy : ℤ)
    (hxlo : -(R : ℤ) < dx) (hxhi : dx < R) :
    ∀ s ∈ (ons_pathVertices (hexCSEastTail R dx)).dropLast,
      0 ≤ (((R : ℤ), 0) + (dx, dy) + s).1 ∧
        (((R : ℤ), 0) + (dx, dy) + s).1 <
          (((2 * R + 1 : ℕ) : ℤ)) := by
  intro s hs
  obtain ⟨k, hk, hkz⟩ :=
    hexCSEastTail_endpoint_vertex_cases R dx dy s hs
  have hlen : 0 ≤ (R : ℤ) + 1 - dx := by omega
  have hk' : (k : ℤ) <
      ((((R : ℤ) + 1 - dx).toNat : ℕ) : ℤ) := by
    exact_mod_cast hk
  rw [Int.toNat_of_nonneg hlen] at hk'
  rw [add_assoc, hkz]
  simp
  omega

theorem hexCSWestNorthEastTail_x_slab
    (R : ℕ) (dx dy : ℤ)
    (hxlo : -(R : ℤ) < dx) (hxhi : dx < R)
    (hyhi : dy < R) :
    ∀ s ∈ (ons_pathVertices
      (hexCSWestNorthEastTail R dx dy)).dropLast,
      0 ≤ (((R : ℤ), 0) + (dx, dy) + s).1 ∧
        (((R : ℤ), 0) + (dx, dy) + s).1 <
          (((2 * R + 1 : ℕ) : ℤ)) := by
  intro s hs
  have hx : 0 ≤ dx + R := by omega
  have hy : 0 ≤ (R : ℤ) - dy := by omega
  rcases hexCSWestNorthEastTail_endpoint_vertex_cases
      R dx dy hx hy s hs with
      ⟨k, hk, hkz⟩ | ⟨k, hk, hkz⟩ | ⟨k, hk, hkz⟩
  · have hk' : (k : ℤ) < (((dx + R).toNat : ℕ) : ℤ) := by
      exact_mod_cast hk
    rw [Int.toNat_of_nonneg hx] at hk'
    rw [add_assoc, hkz]
    simp
    omega
  · rw [add_assoc, hkz]
    simp
  · rw [add_assoc, hkz]
    simp
    omega

theorem hexCSSouthEastTail_x_slab
    (R : ℕ) (dx dy : ℤ)
    (hxlo : -(R : ℤ) < dx) (hxhi : dx < R)
    (hylo : -(R : ℤ) < dy) :
    ∀ s ∈ (ons_pathVertices
      (hexCSSouthEastTail R dx dy)).dropLast,
      0 ≤ (((R : ℤ), 0) + (dx, dy) + s).1 ∧
        (((R : ℤ), 0) + (dx, dy) + s).1 <
          (((2 * R + 1 : ℕ) : ℤ)) := by
  intro s hs
  have hy : 0 ≤ dy + R := by omega
  rcases hexCSSouthEastTail_endpoint_vertex_cases
      R dx dy hy s hs with ⟨k, hk, hkz⟩ | ⟨k, hk, hkz⟩
  · rw [add_assoc, hkz]
    simp
    omega
  · have hlen : 0 ≤ (R : ℤ) + 1 - dx := by omega
    have hk' : (k : ℤ) <
        ((((R : ℤ) + 1 - dx).toNat : ℕ) : ℤ) := by
      exact_mod_cast hk
    rw [Int.toNat_of_nonneg hlen] at hk'
    rw [add_assoc, hkz]
    simp
    omega



theorem hexCS_three_piece_vertices_dropLast_nodup
    (P C S : List (Fin 4))
    (hP : (ons_pathVertices P).dropLast.Nodup)
    (hC : (ons_pathVertices C).dropLast.Nodup)
    (hS : (ons_pathVertices S).dropLast.Nodup)
    (hPC : ∀ p ∈ (ons_pathVertices P).dropLast,
      ∀ c ∈ (ons_pathVertices C).dropLast,
        p ≠ ons_pathDisplacement P + c)
    (hPS : ∀ p ∈ (ons_pathVertices P).dropLast,
      ∀ s ∈ (ons_pathVertices S).dropLast,
        p ≠ ons_pathDisplacement P +
          ons_pathDisplacement C + s)
    (hCS : ∀ c ∈ (ons_pathVertices C).dropLast,
      ∀ s ∈ (ons_pathVertices S).dropLast,
        ons_pathDisplacement P + c ≠
          ons_pathDisplacement P + ons_pathDisplacement C + s) :
    (ons_pathVertices (P ++ C ++ S)).dropLast.Nodup := by
  rw [ons_pathVertices_append_dropLast (P ++ C) S,
    ons_pathVertices_append_dropLast P C,
    ons_pathDisplacement_append]
  have hC' : ((ons_pathVertices C).dropLast.map
      (ons_pathDisplacement P + ·)).Nodup :=
    hC.map (add_right_injective _)
  have hS' : ((ons_pathVertices S).dropLast.map
      (ons_pathDisplacement P + ons_pathDisplacement C + ·)).Nodup :=
    hS.map (add_right_injective _)
  have hPC' : ((ons_pathVertices P).dropLast ++
      (ons_pathVertices C).dropLast.map
        (ons_pathDisplacement P + ·)).Nodup := by
    apply List.Nodup.append hP hC'
    rw [List.disjoint_iff_ne]
    intro p hp q hq
    rw [List.mem_map] at hq
    obtain ⟨c, hc, rfl⟩ := hq
    exact hPC p hp c hc
  apply List.Nodup.append hPC' hS'
  rw [List.disjoint_iff_ne]
  intro q hq r hr
  rw [List.mem_append] at hq
  rw [List.mem_map] at hr
  obtain ⟨s, hs, rfl⟩ := hr
  rcases hq with hp | hc
  · exact hPS q hp s hs
  · rw [List.mem_map] at hc
    obtain ⟨c, hc, rfl⟩ := hc
    exact hCS c hc s hs

theorem hexCSSourceBelow_central_disjoint
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    let R := hexCSBrickRadius T L
    ∀ p ∈ (ons_pathVertices (hexCSSourceBelow R)).dropLast,
      ∀ c ∈ (ons_pathVertices
        (hexCSBrickDirections 1 ts)).dropLast,
        p ≠ ons_pathDisplacement (hexCSSourceBelow R) + c := by
  dsimp only
  let R := hexCSBrickRadius T L
  intro p hp c hc
  rw [hexCSSourceBelow_displacement R]
  rcases hexCSSourceBelow_vertex_cases R p hp with
      ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;>
    rcases hexCSBrickDirections_dropLast_mem_cases
      e ts he hne hadm c hc with rfl | ⟨q, hq, rfl⟩
  · intro h
    change ((k : ℤ), 0) = ((R : ℤ), (R : ℤ)) at h
    rw [Prod.mk.injEq] at h
    have hR : 0 < (R : ℤ) := by
      dsimp [R, hexCSBrickRadius]
      omega
    omega
  · have hb := hexCS_inside_brick_bounds q hq
    dsimp only at hb
    let qx := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).1
    let qy := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2
    change (-(R : ℤ) < qx ∧ qx < R ∧
      -(R : ℤ) < qy ∧ qy < R) at hb
    intro h
    change ((k : ℤ), 0) = ((R : ℤ) + qx, (R : ℤ) + qy) at h
    rw [Prod.mk.injEq] at h
    omega
  · intro h
    change (((2 * R : ℕ) : ℤ), (k : ℤ)) =
      ((R : ℤ), (R : ℤ)) at h
    rw [Prod.mk.injEq] at h
    omega
  · have hb := hexCS_inside_brick_bounds q hq
    dsimp only at hb
    let qx := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).1
    let qy := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2
    change (-(R : ℤ) < qx ∧ qx < R ∧
      -(R : ℤ) < qy ∧ qy < R) at hb
    intro h
    change (((2 * R : ℕ) : ℤ), (k : ℤ)) =
      ((R : ℤ) + qx, (R : ℤ) + qy) at h
    rw [Prod.mk.injEq] at h
    omega
  · intro h
    change ((2 * R : ℤ) - k, (R : ℤ)) =
      ((R : ℤ), (R : ℤ)) at h
    rw [Prod.mk.injEq] at h
    omega
  · have hd := hexCS_inside_brick_depth_pos q hq
    let qx := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).1
    let qy := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2
    change 0 < qy - qx at hd
    intro h
    change ((2 * R : ℤ) - k, (R : ℤ)) =
      ((R : ℤ) + qx, (R : ℤ) + qy) at h
    rw [Prod.mk.injEq] at h
    omega

theorem hexCSSourceAbove_central_disjoint
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    let R := hexCSBrickRadius T L
    ∀ p ∈ (ons_pathVertices (hexCSSourceAbove R)).dropLast,
      ∀ c ∈ (ons_pathVertices
        (hexCSBrickDirections 1 ts)).dropLast,
        p ≠ ons_pathDisplacement (hexCSSourceAbove R) + c := by
  dsimp only
  let R := hexCSBrickRadius T L
  intro p hp c hc
  rw [hexCSSourceAbove_displacement R]
  rcases hexCSSourceAbove_vertex_cases R p hp with
      ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;>
    rcases hexCSBrickDirections_dropLast_mem_cases
      e ts he hne hadm c hc with rfl | ⟨q, hq, rfl⟩
  · intro h
    change ((k : ℤ), 0) = ((R : ℤ), -(R : ℤ)) at h
    rw [Prod.mk.injEq] at h
    have hR : 0 < (R : ℤ) := by
      dsimp [R, hexCSBrickRadius]
      omega
    omega
  · have hb := hexCS_inside_brick_bounds q hq
    dsimp only at hb
    let qx := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).1
    let qy := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2
    change (-(R : ℤ) < qx ∧ qx < R ∧
      -(R : ℤ) < qy ∧ qy < R) at hb
    intro h
    change ((k : ℤ), 0) = ((R : ℤ) + qx, -(R : ℤ) + qy) at h
    rw [Prod.mk.injEq] at h
    omega
  · intro h
    change (((2 * R : ℕ) : ℤ), -(k : ℤ)) =
      ((R : ℤ), -(R : ℤ)) at h
    rw [Prod.mk.injEq] at h
    omega
  · have hb := hexCS_inside_brick_bounds q hq
    dsimp only at hb
    let qx := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).1
    let qy := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2
    change (-(R : ℤ) < qx ∧ qx < R ∧
      -(R : ℤ) < qy ∧ qy < R) at hb
    intro h
    change (((2 * R : ℕ) : ℤ), -(k : ℤ)) =
      ((R : ℤ) + qx, -(R : ℤ) + qy) at h
    rw [Prod.mk.injEq] at h
    omega
  · intro h
    change ((2 * R : ℤ) - k, -(R : ℤ)) =
      ((R : ℤ), -(R : ℤ)) at h
    rw [Prod.mk.injEq] at h
    omega
  · have hd := hexCS_inside_brick_depth_pos q hq
    let qx := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).1
    let qy := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2
    change 0 < qy - qx at hd
    intro h
    change ((2 * R : ℤ) - k, -(R : ℤ)) =
      ((R : ℤ) + qx, -(R : ℤ) + qy) at h
    rw [Prod.mk.injEq] at h
    omega



theorem hexCSBelowEastPeriod_vertices_dropLast_nodup
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge))
    (hside :
      (e.vtx.1.color = .black ∧ e.edge = 0 ∧
        hexAWDepth e.vtx.1 = 0) ∨
      (e.vtx.1.color = .white ∧ e.edge = 1 ∧
        e.vtx.1.i = L))
    (hdy : 0 < (hexCSEndDelta e).2) :
    let R := hexCSBrickRadius T L
    let C := hexCSBrickDirections 1 ts
    (ons_pathVertices
      (hexCSSourceBelow R ++ C ++
        hexCSEastTail R (hexCSEndDelta e).1)).dropLast.Nodup := by
  dsimp only
  let R := hexCSBrickRadius T L
  let C := hexCSBrickDirections 1 ts
  let dx := (hexCSEndDelta e).1
  let dy := (hexCSEndDelta e).2
  apply hexCS_three_piece_vertices_dropLast_nodup
  · exact hexCSSourceBelow_vertices_dropLast_nodup R
  · exact List.Nodup.sublist (List.dropLast_sublist _)
      (hexCSBrickDirections_vertices_nodup e ts he hne hadm)
  · exact hexCSEastTail_vertices_dropLast_nodup R dx
  · exact hexCSSourceBelow_central_disjoint e ts he hne hadm
  · intro p hp s hs
    rw [hexCSSourceBelow_displacement,
      hexCSBrickDirections_displacement e ts he hne hadm]
    obtain ⟨k, hk, hkz⟩ :=
      hexCSEastTail_endpoint_vertex_cases R dx dy s hs
    change (dx, dy) + s = _ at hkz
    rw [add_assoc, hkz]
    rcases hexCSSourceBelow_vertex_cases R p hp with
        ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    all_goals
      intro h
      have hy := congrArg (fun z : ℤ × ℤ => z.2) h
      simp [dy] at hy
      omega
  · intro c hc s hs
    rw [hexCSSourceBelow_displacement,
      hexCSBrickDirections_displacement e ts he hne hadm]
    obtain ⟨k, hk, hkz⟩ :=
      hexCSEastTail_endpoint_vertex_cases R dx dy s hs
    change (dx, dy) + s = _ at hkz
    intro h
    have hcancel : c = (dx, dy) + s := by
      exact add_left_cancel (a := ((R : ℤ), (R : ℤ)))
        (by simpa [dx, dy, add_assoc, Prod.ext_iff] using h)
    rcases hexCSBrickDirections_dropLast_mem_cases
        e ts he hne hadm c hc with rfl | ⟨q, hq, rfl⟩
    · rw [hkz] at hcancel
      have hy := congrArg (fun z : ℤ × ℤ => z.2) hcancel
      simp [dy] at hy
      omega
    · apply hexCSEastRay_not_inside e he hside q hq k
      calc
        hexBrickPos q - hexBrickPos hexCSOutsideStartCoord =
            (dx, dy) + s := hcancel
        _ = (dx, dy) + ((k : ℤ), 0) := by
          simpa using hkz
        _ = hexCSEndDelta e + ((k : ℤ), 0) := by
          simp [dx, dy, Prod.ext_iff]

theorem hexCSAboveEastPeriod_vertices_dropLast_nodup
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge))
    (hside :
      e.vtx.1.color = .black ∧ e.edge = 0 ∧
        hexAWDepth e.vtx.1 = 0)
    (hdy : (hexCSEndDelta e).2 < 0) :
    let R := hexCSBrickRadius T L
    let C := hexCSBrickDirections 1 ts
    (ons_pathVertices
      (hexCSSourceAbove R ++ C ++
        hexCSEastTail R (hexCSEndDelta e).1)).dropLast.Nodup := by
  dsimp only
  let R := hexCSBrickRadius T L
  let C := hexCSBrickDirections 1 ts
  let dx := (hexCSEndDelta e).1
  let dy := (hexCSEndDelta e).2
  apply hexCS_three_piece_vertices_dropLast_nodup
  · exact hexCSSourceAbove_vertices_dropLast_nodup R
  · exact List.Nodup.sublist (List.dropLast_sublist _)
      (hexCSBrickDirections_vertices_nodup e ts he hne hadm)
  · exact hexCSEastTail_vertices_dropLast_nodup R dx
  · exact hexCSSourceAbove_central_disjoint e ts he hne hadm
  · intro p hp s hs
    rw [hexCSSourceAbove_displacement,
      hexCSBrickDirections_displacement e ts he hne hadm]
    obtain ⟨k, hk, hkz⟩ :=
      hexCSEastTail_endpoint_vertex_cases R dx dy s hs
    change (dx, dy) + s = _ at hkz
    rw [add_assoc, hkz]
    rcases hexCSSourceAbove_vertex_cases R p hp with
        ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    all_goals
      intro h
      have hy := congrArg (fun z : ℤ × ℤ => z.2) h
      simp [dy] at hy
      omega
  · intro c hc s hs
    rw [hexCSSourceAbove_displacement,
      hexCSBrickDirections_displacement e ts he hne hadm]
    obtain ⟨k, hk, hkz⟩ :=
      hexCSEastTail_endpoint_vertex_cases R dx dy s hs
    change (dx, dy) + s = _ at hkz
    intro h
    have hcancel : c = (dx, dy) + s := by
      exact add_left_cancel (a := ((R : ℤ), -(R : ℤ)))
        (by simpa [dx, dy, add_assoc, Prod.ext_iff] using h)
    rcases hexCSBrickDirections_dropLast_mem_cases
        e ts he hne hadm c hc with rfl | ⟨q, hq, rfl⟩
    · rw [hkz] at hcancel
      have hy := congrArg (fun z : ℤ × ℤ => z.2) hcancel
      simp [dy] at hy
      omega
    · apply hexCSEastRay_not_inside e he (Or.inl hside) q hq k
      calc
        hexBrickPos q - hexBrickPos hexCSOutsideStartCoord =
            (dx, dy) + s := hcancel
        _ = (dx, dy) + ((k : ℤ), 0) := by
          simpa using hkz
        _ = hexCSEndDelta e + ((k : ℤ), 0) := by
          simp [dx, dy, Prod.ext_iff]

theorem hexCSRightPeriod_vertices_dropLast_nodup
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge))
    (hside : e.vtx.1.color = .white ∧ e.edge = 0 ∧
      hexAWDepth e.vtx.1 = T) :
    let R := hexCSBrickRadius T L
    let C := hexCSBrickDirections 1 ts
    (ons_pathVertices
      (hexCSSourceBelow R ++ C ++
        hexCSWestNorthEastTail R (hexCSEndDelta e).1
          (hexCSEndDelta e).2)).dropLast.Nodup := by
  dsimp only
  let R := hexCSBrickRadius T L
  let C := hexCSBrickDirections 1 ts
  let dx := (hexCSEndDelta e).1
  let dy := (hexCSEndDelta e).2
  have hb := hexCSEndDelta_bounds (hT := hT) e he
  dsimp only at hb
  change (-(R : ℤ) < dx ∧ dx < R ∧
    -(R : ℤ) < dy ∧ dy < R) at hb
  have hzero : dy = 0 → dx < 0 := by
    intro hy
    exact hexCSEndDelta_right_zero_height (hT := hT) e he
      hside.1 hside.2.1 hy
  have hR : 0 < (R : ℤ) := by
    dsimp [R, hexCSBrickRadius]
    omega
  apply hexCS_three_piece_vertices_dropLast_nodup
  · exact hexCSSourceBelow_vertices_dropLast_nodup R
  · exact List.Nodup.sublist (List.dropLast_sublist _)
      (hexCSBrickDirections_vertices_nodup e ts he hne hadm)
  · exact hexCSWestNorthEastTail_vertices_dropLast_nodup
      R dx dy (by omega) (by omega)
  · exact hexCSSourceBelow_central_disjoint e ts he hne hadm
  · intro p hp s hs
    rw [hexCSSourceBelow_displacement,
      hexCSBrickDirections_displacement e ts he hne hadm]
    have hx : 0 ≤ dx + R := by omega
    have hy : 0 ≤ (R : ℤ) - dy := by omega
    rcases hexCSWestNorthEastTail_endpoint_vertex_cases
        R dx dy hx hy s hs with
        ⟨k, hk, hkz⟩ | ⟨k, hk, hkz⟩ | ⟨k, hk, hkz⟩ <;>
      rcases hexCSSourceBelow_vertex_cases R p hp with
        ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    all_goals
      rw [add_assoc, hkz]
      intro h
      have hxx := congrArg (fun z : ℤ × ℤ => z.1) h
      have hyy := congrArg (fun z : ℤ × ℤ => z.2) h
      simp at hxx hyy
      by_cases hy0 : dy = 0
      · have hdx := hzero hy0
        omega
      · omega
  · intro c hc s hs
    rw [hexCSSourceBelow_displacement,
      hexCSBrickDirections_displacement e ts he hne hadm]
    have hx : 0 ≤ dx + R := by omega
    have hy : 0 ≤ (R : ℤ) - dy := by omega
    rcases hexCSWestNorthEastTail_endpoint_vertex_cases
        R dx dy hx hy s hs with
        ⟨k, hk, hkz⟩ | ⟨k, hk, hkz⟩ | ⟨k, hk, hkz⟩
    · intro h
      have hcancel : c = (dx, dy) + s :=
        add_left_cancel (a := ((R : ℤ), (R : ℤ)))
          (by simpa [dx, dy, add_assoc, Prod.ext_iff] using h)
      rcases hexCSBrickDirections_dropLast_mem_cases
          e ts he hne hadm c hc with rfl | ⟨q, hq, rfl⟩
      · rw [hkz] at hcancel
        have hxx := congrArg (fun z : ℤ × ℤ => z.1) hcancel
        have hyy := congrArg (fun z : ℤ × ℤ => z.2) hcancel
        simp at hxx hyy
        by_cases hy0 : dy = 0
        · have hdx := hzero hy0
          omega
        · omega
      · apply hexCSWestRay_not_inside e hside q hq k
        calc
          hexBrickPos q - hexBrickPos hexCSOutsideStartCoord =
              (dx, dy) + s := hcancel
          _ = (dx, dy) + (-(k : ℤ), 0) := by
            simpa using hkz
          _ = hexCSEndDelta e + (-(k : ℤ), 0) := by
            simp [dx, dy, Prod.ext_iff]
    · intro h
      have hcancel : c = (dx, dy) + s :=
        add_left_cancel (a := ((R : ℤ), (R : ℤ)))
          (by simpa [dx, dy, add_assoc, Prod.ext_iff] using h)
      rw [hkz] at hcancel
      rcases hexCSBrickDirections_dropLast_mem_cases
          e ts he hne hadm c hc with rfl | ⟨q, hqmem, hqeq⟩
      · have hx0 := congrArg (fun z : ℤ × ℤ => z.1) hcancel
        simp at hx0
        omega
      · have hqbound := hexCS_inside_brick_bounds q hqmem
        dsimp only at hqbound
        let qx := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).1
        let qy := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2
        change (-(R : ℤ) < qx ∧ qx < R ∧
          -(R : ℤ) < qy ∧ qy < R) at hqbound
        rw [hqeq] at hcancel
        change (qx, qy) = (-(R : ℤ), dy + k) at hcancel
        rw [Prod.mk.injEq] at hcancel
        omega
    · intro h
      have hcancel : c = (dx, dy) + s :=
        add_left_cancel (a := ((R : ℤ), (R : ℤ)))
          (by simpa [dx, dy, add_assoc, Prod.ext_iff] using h)
      rw [hkz] at hcancel
      rcases hexCSBrickDirections_dropLast_mem_cases
          e ts he hne hadm c hc with rfl | ⟨q, hqmem, hqeq⟩
      · have hy0 := congrArg (fun z : ℤ × ℤ => z.2) hcancel
        simp at hy0
        omega
      · have hqbound := hexCS_inside_brick_bounds q hqmem
        dsimp only at hqbound
        let qx := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).1
        let qy := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2
        change (-(R : ℤ) < qx ∧ qx < R ∧
          -(R : ℤ) < qy ∧ qy < R) at hqbound
        rw [hqeq] at hcancel
        change (qx, qy) = (-(R : ℤ) + k, (R : ℤ)) at hcancel
        rw [Prod.mk.injEq] at hcancel
        omega

theorem hexCSLowerPeriod_vertices_dropLast_nodup
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge))
    (hside : e.vtx.1.color = .white ∧ e.edge = 2 ∧
      e.vtx.1.j = L) :
    let R := hexCSBrickRadius T L
    let C := hexCSBrickDirections 1 ts
    (ons_pathVertices
      (hexCSSourceAbove R ++ C ++
        hexCSSouthEastTail R (hexCSEndDelta e).1
          (hexCSEndDelta e).2)).dropLast.Nodup := by
  dsimp only
  let R := hexCSBrickRadius T L
  let C := hexCSBrickDirections 1 ts
  let dx := (hexCSEndDelta e).1
  let dy := (hexCSEndDelta e).2
  have hb := hexCSEndDelta_bounds (hT := hT) e he
  dsimp only at hb
  change (-(R : ℤ) < dx ∧ dx < R ∧
    -(R : ℤ) < dy ∧ dy < R) at hb
  have hdy : dy < 0 :=
    (hexCSEndDelta_slant_sign e he).2 ⟨hside.1, hside.2.1⟩
  have hR : 0 < (R : ℤ) := by
    dsimp [R, hexCSBrickRadius]
    omega
  apply hexCS_three_piece_vertices_dropLast_nodup
  · exact hexCSSourceAbove_vertices_dropLast_nodup R
  · exact List.Nodup.sublist (List.dropLast_sublist _)
      (hexCSBrickDirections_vertices_nodup e ts he hne hadm)
  · exact hexCSSouthEastTail_vertices_dropLast_nodup
      R dx dy (by omega)
  · exact hexCSSourceAbove_central_disjoint e ts he hne hadm
  · intro p hp s hs
    rw [hexCSSourceAbove_displacement,
      hexCSBrickDirections_displacement e ts he hne hadm]
    have hy : 0 ≤ dy + R := by omega
    rcases hexCSSouthEastTail_endpoint_vertex_cases
        R dx dy hy s hs with ⟨k, hk, hkz⟩ | ⟨k, hk, hkz⟩ <;>
      rcases hexCSSourceAbove_vertex_cases R p hp with
        ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    all_goals
      rw [add_assoc, hkz]
      intro h
      have hxx := congrArg (fun z : ℤ × ℤ => z.1) h
      have hyy := congrArg (fun z : ℤ × ℤ => z.2) h
      simp at hxx hyy
      omega
  · intro c hc s hs
    rw [hexCSSourceAbove_displacement,
      hexCSBrickDirections_displacement e ts he hne hadm]
    have hy : 0 ≤ dy + R := by omega
    rcases hexCSSouthEastTail_endpoint_vertex_cases
        R dx dy hy s hs with ⟨k, hk, hkz⟩ | ⟨k, hk, hkz⟩
    · intro h
      have hcancel : c = (dx, dy) + s :=
        add_left_cancel (a := ((R : ℤ), -(R : ℤ)))
          (by simpa [dx, dy, add_assoc, Prod.ext_iff] using h)
      rcases hexCSBrickDirections_dropLast_mem_cases
          e ts he hne hadm c hc with rfl | ⟨q, hq, rfl⟩
      · rw [hkz] at hcancel
        have hyy := congrArg (fun z : ℤ × ℤ => z.2) hcancel
        simp at hyy
        omega
      · apply hexCSSouthRay_not_inside e hside q hq k
        calc
          hexBrickPos q - hexBrickPos hexCSOutsideStartCoord =
              (dx, dy) + s := hcancel
          _ = (dx, dy) + (0, -(k : ℤ)) := by
            simpa using hkz
          _ = hexCSEndDelta e + (0, -(k : ℤ)) := by
            simp [dx, dy, Prod.ext_iff]
    · intro h
      have hcancel : c = (dx, dy) + s :=
        add_left_cancel (a := ((R : ℤ), -(R : ℤ)))
          (by simpa [dx, dy, add_assoc, Prod.ext_iff] using h)
      rw [hkz] at hcancel
      rcases hexCSBrickDirections_dropLast_mem_cases
          e ts he hne hadm c hc with rfl | ⟨q, hqmem, hqeq⟩
      · have hy0 := congrArg (fun z : ℤ × ℤ => z.2) hcancel
        simp at hy0
        omega
      · have hqbound := hexCS_inside_brick_bounds q hqmem
        dsimp only at hqbound
        let qx := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).1
        let qy := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2
        change (-(R : ℤ) < qx ∧ qx < R ∧
          -(R : ℤ) < qy ∧ qy < R) at hqbound
        rw [hqeq] at hcancel
        change (qx, qy) = (dx + k, -(R : ℤ)) at hcancel
        rw [Prod.mk.injEq] at hcancel
        omega



theorem hexCSBelowEastPeriod_cyclicTurnSum_eq_zero
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge))
    (hside :
      (e.vtx.1.color = .black ∧ e.edge = 0 ∧
        hexAWDepth e.vtx.1 = 0) ∨
      (e.vtx.1.color = .white ∧ e.edge = 1 ∧
        e.vtx.1.i = L))
    (hdy : 0 < (hexCSEndDelta e).2) :
    let R := hexCSBrickRadius T L
    let C := hexCSBrickDirections 1 ts
    ons_cyclicTurnSum
      (hexCSSourceBelow R ++ C ++
        hexCSEastTail R (hexCSEndDelta e).1) = 0 := by
  dsimp only
  let R := hexCSBrickRadius T L
  let C := hexCSBrickDirections 1 ts
  let dx := (hexCSEndDelta e).1
  let dy := (hexCSEndDelta e).2
  let l := hexCSSourceBelow R ++ C ++ hexCSEastTail R dx
  have hb := hexCSEndDelta_bounds (hT := hT) e he
  dsimp only at hb
  change (-(R : ℤ) < dx ∧ dx < R ∧
    -(R : ℤ) < dy ∧ dy < R) at hb
  have hC : C ≠ [] := hexCSBrickDirections_ne_nil 1 ts
  letI : NeZero l.length := ⟨by simp [l, hC]⟩
  apply hexCS_cyclicTurnSum_eq_zero_of_slab l
    (2 * R + 1) (R + dy)
  · dsimp [l]
    rw [ons_pathDisplacement_append,
      ons_pathDisplacement_append,
      hexCSSourceBelow_displacement,
      hexCSBrickDirections_displacement e ts he hne hadm,
      hexCSEastTail_displacement R dx (by omega)]
    ext <;> simp [dx, dy] <;> omega
  · omega
  · exact hexCSBelowEastPeriod_vertices_dropLast_nodup
      e ts he hne hadm hside hdy
  · dsimp [l]
    apply hexCS_three_piece_x_slab
    · exact hexCSSourceBelow_x_slab R
    · intro c hc
      rw [hexCSSourceBelow_displacement]
      simpa using hexCS_central_x_slab e ts he hne hadm c hc
    · intro s hs
      rw [hexCSSourceBelow_displacement,
        hexCSBrickDirections_displacement e ts he hne hadm]
      simpa [dx, dy] using
        hexCSEastTail_x_slab R dx dy hb.1 hb.2.1 s hs

theorem hexCSAboveEastPeriod_cyclicTurnSum_eq_zero
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge))
    (hside : e.vtx.1.color = .black ∧ e.edge = 0 ∧
      hexAWDepth e.vtx.1 = 0)
    (hdy : (hexCSEndDelta e).2 < 0) :
    let R := hexCSBrickRadius T L
    let C := hexCSBrickDirections 1 ts
    ons_cyclicTurnSum
      (hexCSSourceAbove R ++ C ++
        hexCSEastTail R (hexCSEndDelta e).1) = 0 := by
  dsimp only
  let R := hexCSBrickRadius T L
  let C := hexCSBrickDirections 1 ts
  let dx := (hexCSEndDelta e).1
  let dy := (hexCSEndDelta e).2
  let l := hexCSSourceAbove R ++ C ++ hexCSEastTail R dx
  have hb := hexCSEndDelta_bounds (hT := hT) e he
  dsimp only at hb
  change (-(R : ℤ) < dx ∧ dx < R ∧
    -(R : ℤ) < dy ∧ dy < R) at hb
  have hC : C ≠ [] := hexCSBrickDirections_ne_nil 1 ts
  letI : NeZero l.length := ⟨by simp [l, hC]⟩
  apply hexCS_cyclicTurnSum_eq_zero_of_slab l
    (2 * R + 1) (-R + dy)
  · dsimp [l]
    rw [ons_pathDisplacement_append,
      ons_pathDisplacement_append,
      hexCSSourceAbove_displacement,
      hexCSBrickDirections_displacement e ts he hne hadm,
      hexCSEastTail_displacement R dx (by omega)]
    ext <;> simp [dx, dy] <;> omega
  · omega
  · exact hexCSAboveEastPeriod_vertices_dropLast_nodup
      e ts he hne hadm hside hdy
  · dsimp [l]
    apply hexCS_three_piece_x_slab
    · exact hexCSSourceAbove_x_slab R
    · intro c hc
      rw [hexCSSourceAbove_displacement]
      simpa using hexCS_central_x_slab e ts he hne hadm c hc
    · intro s hs
      rw [hexCSSourceAbove_displacement,
        hexCSBrickDirections_displacement e ts he hne hadm]
      simpa [dx, dy] using
        hexCSEastTail_x_slab R dx dy hb.1 hb.2.1 s hs

theorem hexCSRightPeriod_cyclicTurnSum_eq_zero
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge))
    (hside : e.vtx.1.color = .white ∧ e.edge = 0 ∧
      hexAWDepth e.vtx.1 = T) :
    let R := hexCSBrickRadius T L
    let C := hexCSBrickDirections 1 ts
    ons_cyclicTurnSum
      (hexCSSourceBelow R ++ C ++
        hexCSWestNorthEastTail R (hexCSEndDelta e).1
          (hexCSEndDelta e).2) = 0 := by
  dsimp only
  let R := hexCSBrickRadius T L
  let C := hexCSBrickDirections 1 ts
  let dx := (hexCSEndDelta e).1
  let dy := (hexCSEndDelta e).2
  let S := hexCSWestNorthEastTail R dx dy
  let l := hexCSSourceBelow R ++ C ++ S
  have hb := hexCSEndDelta_bounds (hT := hT) e he
  dsimp only at hb
  change (-(R : ℤ) < dx ∧ dx < R ∧
    -(R : ℤ) < dy ∧ dy < R) at hb
  have hC : C ≠ [] := hexCSBrickDirections_ne_nil 1 ts
  letI : NeZero l.length := ⟨by simp [l, hC]⟩
  apply hexCS_cyclicTurnSum_eq_zero_of_slab l
    (2 * R + 1) (2 * R)
  · dsimp [l, S]
    rw [ons_pathDisplacement_append,
      ons_pathDisplacement_append,
      hexCSSourceBelow_displacement,
      hexCSBrickDirections_displacement e ts he hne hadm,
      hexCSWestNorthEastTail_displacement R dx dy
        (by omega) (by omega)]
    ext <;> simp [dx, dy] <;> omega
  · omega
  · exact hexCSRightPeriod_vertices_dropLast_nodup
      e ts he hne hadm hside
  · dsimp [l, S]
    apply hexCS_three_piece_x_slab
    · exact hexCSSourceBelow_x_slab R
    · intro c hc
      rw [hexCSSourceBelow_displacement]
      simpa using hexCS_central_x_slab e ts he hne hadm c hc
    · intro s hs
      rw [hexCSSourceBelow_displacement,
        hexCSBrickDirections_displacement e ts he hne hadm]
      simpa [dx, dy] using
        hexCSWestNorthEastTail_x_slab R dx dy
          hb.1 hb.2.1 hb.2.2.2 s hs

theorem hexCSLowerPeriod_cyclicTurnSum_eq_zero
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge))
    (hside : e.vtx.1.color = .white ∧ e.edge = 2 ∧
      e.vtx.1.j = L) :
    let R := hexCSBrickRadius T L
    let C := hexCSBrickDirections 1 ts
    ons_cyclicTurnSum
      (hexCSSourceAbove R ++ C ++
        hexCSSouthEastTail R (hexCSEndDelta e).1
          (hexCSEndDelta e).2) = 0 := by
  dsimp only
  let R := hexCSBrickRadius T L
  let C := hexCSBrickDirections 1 ts
  let dx := (hexCSEndDelta e).1
  let dy := (hexCSEndDelta e).2
  let S := hexCSSouthEastTail R dx dy
  let l := hexCSSourceAbove R ++ C ++ S
  have hb := hexCSEndDelta_bounds (hT := hT) e he
  dsimp only at hb
  change (-(R : ℤ) < dx ∧ dx < R ∧
    -(R : ℤ) < dy ∧ dy < R) at hb
  have hC : C ≠ [] := hexCSBrickDirections_ne_nil 1 ts
  letI : NeZero l.length := ⟨by simp [l, hC]⟩
  apply hexCS_cyclicTurnSum_eq_zero_of_slab l
    (2 * R + 1) (-2 * R)
  · dsimp [l, S]
    rw [ons_pathDisplacement_append,
      ons_pathDisplacement_append,
      hexCSSourceAbove_displacement,
      hexCSBrickDirections_displacement e ts he hne hadm,
      hexCSSouthEastTail_displacement R dx dy
        (by omega) (by omega)]
    ext <;> simp [dx, dy] <;> omega
  · omega
  · exact hexCSLowerPeriod_vertices_dropLast_nodup
      e ts he hne hadm hside
  · dsimp [l, S]
    apply hexCS_three_piece_x_slab
    · exact hexCSSourceAbove_x_slab R
    · intro c hc
      rw [hexCSSourceAbove_displacement]
      simpa using hexCS_central_x_slab e ts he hne hadm c hc
    · intro s hs
      rw [hexCSSourceAbove_displacement,
        hexCSBrickDirections_displacement e ts he hne hadm]
      simpa [dx, dy] using
        hexCSSouthEastTail_x_slab R dx dy
          hb.1 hb.2.1 hb.2.2.1 s hs



theorem hexCSSourceBelow_ne_nil (R : ℕ) (hR : 0 < R) :
    hexCSSourceBelow R ≠ [] := by
  simp [hexCSSourceBelow, Nat.ne_of_gt hR]

theorem hexCSSourceAbove_ne_nil (R : ℕ) (hR : 0 < R) :
    hexCSSourceAbove R ≠ [] := by
  simp [hexCSSourceAbove, Nat.ne_of_gt hR]

theorem hexCSSourceBelow_head (R : ℕ) (hR : 0 < R) :
    (hexCSSourceBelow R).head! = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hR)
  rw [hexCSSourceBelow, show 2 * (r + 1) = (2 * r + 1) + 1 by omega,
    List.replicate_succ]
  rfl

theorem hexCSSourceAbove_head (R : ℕ) (hR : 0 < R) :
    (hexCSSourceAbove R).head! = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hR)
  rw [hexCSSourceAbove, show 2 * (r + 1) = (2 * r + 1) + 1 by omega,
    List.replicate_succ]
  rfl

theorem hexCSSourceBelow_getLast (R : ℕ) (hR : 0 < R) :
    (hexCSSourceBelow R).getLast! = 2 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hR)
  rw [hexCSSourceBelow,
    ons_getLast!_append_of_right_ne_nil _ _ (by simp)]
  simp

theorem hexCSSourceAbove_getLast (R : ℕ) (hR : 0 < R) :
    (hexCSSourceAbove R).getLast! = 2 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hR)
  rw [hexCSSourceAbove,
    ons_getLast!_append_of_right_ne_nil _ _ (by simp)]
  simp

theorem hexCSEastTail_ne_nil (R : ℕ) (dx : ℤ)
    (h : 0 < (R : ℤ) + 1 - dx) :
    hexCSEastTail R dx ≠ [] := by
  simp [hexCSEastTail, Int.toNat_eq_zero]
  omega

theorem hexCSEastTail_head (R : ℕ) (dx : ℤ)
    (h : 0 < (R : ℤ) + 1 - dx) :
    (hexCSEastTail R dx).head! = 0 := by
  obtain ⟨n, hn⟩ : ∃ n, ((R : ℤ) + 1 - dx).toNat = n + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    intro hz
    have := Int.toNat_eq_zero.mp hz
    omega
  simp [hexCSEastTail, hn]

theorem hexCSEastTail_getLast (R : ℕ) (dx : ℤ)
    (h : 0 < (R : ℤ) + 1 - dx) :
    (hexCSEastTail R dx).getLast! = 0 := by
  obtain ⟨n, hn⟩ : ∃ n, ((R : ℤ) + 1 - dx).toNat = n + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    intro hz
    have := Int.toNat_eq_zero.mp hz
    omega
  rw [hexCSEastTail, hn]
  exact ons_getLast_replicate_succ n 0

theorem hexCSWestNorthEastTail_ne_nil
    (R : ℕ) (dx dy : ℤ) (hW : 0 < dx + R) :
    hexCSWestNorthEastTail R dx dy ≠ [] := by
  obtain ⟨n, hn⟩ : ∃ n, (dx + R).toNat = n + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    intro hz
    have := Int.toNat_eq_zero.mp hz
    omega
  simp [hexCSWestNorthEastTail, hn]

theorem hexCSWestNorthEastTail_head
    (R : ℕ) (dx dy : ℤ) (hW : 0 < dx + R) :
    (hexCSWestNorthEastTail R dx dy).head! = 2 := by
  obtain ⟨n, hn⟩ : ∃ n, (dx + R).toNat = n + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    intro hz
    have := Int.toNat_eq_zero.mp hz
    omega
  simp [hexCSWestNorthEastTail, hn]

theorem hexCSWestNorthEastTail_getLast
    (R : ℕ) (dx dy : ℤ) :
    (hexCSWestNorthEastTail R dx dy).getLast! = 0 := by
  rw [hexCSWestNorthEastTail,
    ons_getLast!_append_of_right_ne_nil _ _ (by simp)]
  simp

theorem hexCSSouthEastTail_ne_nil
    (R : ℕ) (dx dy : ℤ) (hS : 0 < dy + R) :
    hexCSSouthEastTail R dx dy ≠ [] := by
  obtain ⟨n, hn⟩ : ∃ n, (dy + R).toNat = n + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    intro hz
    have := Int.toNat_eq_zero.mp hz
    omega
  simp [hexCSSouthEastTail, hn]

theorem hexCSSouthEastTail_head
    (R : ℕ) (dx dy : ℤ) (hS : 0 < dy + R) :
    (hexCSSouthEastTail R dx dy).head! = 3 := by
  obtain ⟨n, hn⟩ : ∃ n, (dy + R).toNat = n + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    intro hz
    have := Int.toNat_eq_zero.mp hz
    omega
  simp [hexCSSouthEastTail, hn]

theorem hexCSSouthEastTail_getLast
    (R : ℕ) (dx dy : ℤ)
    (hE : 0 < (R : ℤ) + 1 - dx) :
    (hexCSSouthEastTail R dx dy).getLast! = 0 := by
  obtain ⟨n, hn⟩ : ∃ n, ((R : ℤ) + 1 - dx).toNat = n + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    intro hz
    have := Int.toNat_eq_zero.mp hz
    omega
  rw [hexCSSouthEastTail,
    ons_getLast!_append_of_right_ne_nil _ _ (by simp [hn]), hn]
  exact ons_getLast_replicate_succ n 0



theorem hexCS_cyclicTurnSum_three_piece
    (P C S : List (Fin 4))
    (hP : P ≠ []) (hC : C ≠ []) (hS : S ≠ [])
    (hPhead : P.head! = 0) (hPlast : P.getLast! = 2)
    (hChead : C.head! = 2)
    (hjoin : C.getLast! = S.head!)
    (hSlast : S.getLast! = 0) :
    ons_cyclicTurnSum (P ++ C ++ S) =
      ons_openTurnSum P + ons_openTurnSum C + ons_openTurnSum S := by
  have hPC : P ++ C ≠ [] := List.append_ne_nil_of_right_ne_nil P hC
  have hl : P ++ C ++ S ≠ [] :=
    List.append_ne_nil_of_right_ne_nil (P ++ C) hS
  have hhead : (P ++ C ++ S).head! = P.head! := by
    simp [hP]
  have hlast : (P ++ C ++ S).getLast! = S.getLast! := by
    exact ons_getLast!_append_of_right_ne_nil (P ++ C) S hS
  have hPClast : (P ++ C).getLast! = C.getLast! :=
    ons_getLast!_append_of_right_ne_nil P C hC
  have hcyc : ons_cyclicTurnSum (P ++ C ++ S) =
      ons_openTurnSum (P ++ C ++ S) +
        ons_turnPow (P ++ C ++ S).getLast!
          (P ++ C ++ S).head! := by
    obtain ⟨d, ds, hd⟩ := List.exists_cons_of_ne_nil hl
    rw [hd]
    rfl
  rw [hcyc,
    ons_openTurnSum_append (P ++ C) S hPC hS,
    ons_openTurnSum_append P C hP hC,
    hPClast, hjoin, hhead, hlast,
    hPhead, hPlast, hChead, hSlast]
  norm_num [ons_turnPow]

private def hexCSWindowExteriorTurn {T L : ℕ}
    (e : HexCSIncidence T L) : ℤ :=
  match e.vtx.1.color, e.edge with
  | .black, 0 => if 0 ≤ hexAWTrans e.vtx.1 then 2 else -2
  | .white, 0 => 0
  | .white, 1 => 2
  | .white, 2 => -1
  | _, _ => 0

private theorem hexCSHeadingFin_eq_of_dvd_window {h k : ℤ}
    (hdvd : (6 : ℤ) ∣ h - k) :
    hexCSHeadingFin h = hexCSHeadingFin k := by
  apply (ZMod.finEquiv 6).injective
  change (h : ZMod 6) = (k : ZMod 6)
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  rcases hdvd with ⟨q, hq⟩
  exact ⟨-q, by omega⟩

private theorem hexCS_finalHeadingFin_eq_canonical
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    hexCSHeadingFin (hexInfra_headAccum 1 ts) =
      hexCSHeadingFin (hexCSCanonicalHeading e) := by
  apply hexCSHeadingFin_eq_of_dvd_window
  apply hexInfra_finalHeading_mod_of_lastVertex hexAWStart 1
    (hexAWMid e.vtx.1 e.edge) (hexCSCanonicalHeading e) ts hadm.2.2
  exact hexCS_boundaryExitLaw T L hT e ts he hne hadm

private theorem hexCSHeadingFin_four_window :
    hexCSHeadingFin 4 = 4 := by
  apply (ZMod.finEquiv 6).injective
  change (4 : ZMod 6) = (4 : ZMod 6)
  rfl

private theorem hexCSHeadingFin_neg_two_window :
    hexCSHeadingFin (-2) = 4 := by
  apply (ZMod.finEquiv 6).injective
  change (-2 : ZMod 6) = (4 : ZMod 6)
  decide

private theorem hexCSHeadingFin_three_window :
    hexCSHeadingFin 3 = 3 := by
  apply (ZMod.finEquiv 6).injective
  change (3 : ZMod 6) = (3 : ZMod 6)
  rfl

private theorem hexCSHeadingFin_neg_one_window :
    hexCSHeadingFin (-1) = 5 := by
  apply (ZMod.finEquiv 6).injective
  change (-1 : ZMod 6) = (5 : ZMod 6)
  decide

private theorem hexCS_boundaryBrickTurnLaw
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    ons_openTurnSum (hexCSBrickDirections 1 ts) +
      hexCSWindowExteriorTurn e = 0 := by
  let R := hexCSBrickRadius T L
  let C := hexCSBrickDirections 1 ts
  let dx := (hexCSEndDelta e).1
  let dy := (hexCSEndDelta e).2
  have hR : 0 < R := by simp [R, hexCSBrickRadius]
  have hb := hexCSEndDelta_bounds (hT := hT) e he
  dsimp only at hb
  change (-(R : ℤ) < dx ∧ dx < R ∧
    -(R : ℤ) < dy ∧ dy < R) at hb
  have hC : C ≠ [] := hexCSBrickDirections_ne_nil 1 ts
  have hChead : C.head! = 2 := by
    simp [C, hexCSHeadingFin_one, hexBrickDir]
  have hmod := hexCS_finalHeadingFin_eq_canonical
    e ts he hne hadm
  obtain hleft | hright | hupp | hlow :=
    hexCS_boundary_classification e he
  · rcases hleft with ⟨hc, hedge, hdepth⟩
    by_cases hs : 0 ≤ hexAWTrans e.vtx.1
    · have hdy : 0 < dy :=
        (hexCSEndDelta_left_sign e he hne hc hedge).1 hs
      have hE : 0 < (R : ℤ) + 1 - dx := by omega
      have hjoin : C.getLast! = (hexCSEastTail R dx).head! := by
        dsimp only [C]
        rw [hexCSBrickDirections_getLast, hmod,
          hexCSEastTail_head R dx hE]
        simp [hexCSCanonicalHeading, hc, hedge, hs,
          hexCSHeadingFin_four_window, hexBrickDir]
      have hsplit := hexCS_cyclicTurnSum_three_piece
        (hexCSSourceBelow R) C (hexCSEastTail R dx)
        (hexCSSourceBelow_ne_nil R hR) hC
        (hexCSEastTail_ne_nil R dx hE)
        (hexCSSourceBelow_head R hR)
        (hexCSSourceBelow_getLast R hR) hChead hjoin
        (hexCSEastTail_getLast R dx hE)
      have hz := hexCSBelowEastPeriod_cyclicTurnSum_eq_zero
        e ts he hne hadm (Or.inl ⟨hc, hedge, hdepth⟩) hdy
      dsimp only at hz
      change ons_openTurnSum C + hexCSWindowExteriorTurn e = 0
      rw [hsplit, hexCSSourceBelow_openTurn R hR,
        hexCSEastTail_openTurn R dx] at hz
      simp [hexCSWindowExteriorTurn, hc, hedge, hs]
      omega
    · have hdy : dy < 0 :=
        (hexCSEndDelta_left_sign e he hne hc hedge).2 hs
      have hE : 0 < (R : ℤ) + 1 - dx := by omega
      have hjoin : C.getLast! = (hexCSEastTail R dx).head! := by
        dsimp only [C]
        rw [hexCSBrickDirections_getLast, hmod,
          hexCSEastTail_head R dx hE]
        simp [hexCSCanonicalHeading, hc, hedge, hs,
          hexCSHeadingFin_neg_two_window, hexBrickDir]
      have hsplit := hexCS_cyclicTurnSum_three_piece
        (hexCSSourceAbove R) C (hexCSEastTail R dx)
        (hexCSSourceAbove_ne_nil R hR) hC
        (hexCSEastTail_ne_nil R dx hE)
        (hexCSSourceAbove_head R hR)
        (hexCSSourceAbove_getLast R hR) hChead hjoin
        (hexCSEastTail_getLast R dx hE)
      have hz := hexCSAboveEastPeriod_cyclicTurnSum_eq_zero
        e ts he hne hadm ⟨hc, hedge, hdepth⟩ hdy
      dsimp only at hz
      change ons_openTurnSum C + hexCSWindowExteriorTurn e = 0
      rw [hsplit, hexCSSourceAbove_openTurn R hR,
        hexCSEastTail_openTurn R dx] at hz
      simp [hexCSWindowExteriorTurn, hc, hedge, hs]
      omega
  · rcases hright with ⟨hc, hedge, hdepth⟩
    have hW : 0 < dx + R := by omega
    have hN : 0 < (R : ℤ) - dy := by omega
    have hjoin : C.getLast! =
        (hexCSWestNorthEastTail R dx dy).head! := by
      dsimp only [C]
      rw [hexCSBrickDirections_getLast, hmod,
        hexCSWestNorthEastTail_head R dx dy hW]
      simp [hexCSCanonicalHeading, hc, hedge,
        hexCSHeadingFin_one, hexBrickDir]
    have hsplit := hexCS_cyclicTurnSum_three_piece
      (hexCSSourceBelow R) C (hexCSWestNorthEastTail R dx dy)
      (hexCSSourceBelow_ne_nil R hR) hC
      (hexCSWestNorthEastTail_ne_nil R dx dy hW)
      (hexCSSourceBelow_head R hR)
      (hexCSSourceBelow_getLast R hR) hChead hjoin
      (hexCSWestNorthEastTail_getLast R dx dy)
    have hz := hexCSRightPeriod_cyclicTurnSum_eq_zero
      e ts he hne hadm ⟨hc, hedge, hdepth⟩
    dsimp only at hz
    change ons_openTurnSum C + hexCSWindowExteriorTurn e = 0
    rw [hsplit, hexCSSourceBelow_openTurn R hR,
      hexCSWestNorthEastTail_openTurn R dx dy hW hN] at hz
    simp [hexCSWindowExteriorTurn, hc, hedge]
    omega
  · rcases hupp with ⟨hc, hedge, hi⟩
    have hdy : 0 < dy :=
      (hexCSEndDelta_slant_sign e he).1 ⟨hc, hedge⟩
    have hE : 0 < (R : ℤ) + 1 - dx := by omega
    have hjoin : C.getLast! = (hexCSEastTail R dx).head! := by
      dsimp only [C]
      rw [hexCSBrickDirections_getLast, hmod,
        hexCSEastTail_head R dx hE]
      simp [hexCSCanonicalHeading, hc, hedge,
        hexCSHeadingFin_three_window, hexBrickDir]
    have hsplit := hexCS_cyclicTurnSum_three_piece
      (hexCSSourceBelow R) C (hexCSEastTail R dx)
      (hexCSSourceBelow_ne_nil R hR) hC
      (hexCSEastTail_ne_nil R dx hE)
      (hexCSSourceBelow_head R hR)
      (hexCSSourceBelow_getLast R hR) hChead hjoin
      (hexCSEastTail_getLast R dx hE)
    have hz := hexCSBelowEastPeriod_cyclicTurnSum_eq_zero
      e ts he hne hadm (Or.inr ⟨hc, hedge, hi⟩) hdy
    dsimp only at hz
    change ons_openTurnSum C + hexCSWindowExteriorTurn e = 0
    rw [hsplit, hexCSSourceBelow_openTurn R hR,
      hexCSEastTail_openTurn R dx] at hz
    simp [hexCSWindowExteriorTurn, hc, hedge]
    omega
  · rcases hlow with ⟨hc, hedge, hj⟩
    have hdy : dy < 0 :=
      (hexCSEndDelta_slant_sign e he).2 ⟨hc, hedge⟩
    have hS : 0 < dy + R := by omega
    have hE : 0 < (R : ℤ) + 1 - dx := by omega
    have hE' : 0 < (R : ℤ) - dx := by omega
    have hjoin : C.getLast! =
        (hexCSSouthEastTail R dx dy).head! := by
      dsimp only [C]
      rw [hexCSBrickDirections_getLast, hmod,
        hexCSSouthEastTail_head R dx dy hS]
      simp [hexCSCanonicalHeading, hc, hedge,
        hexCSHeadingFin_neg_one_window, hexBrickDir]
    have hsplit := hexCS_cyclicTurnSum_three_piece
      (hexCSSourceAbove R) C (hexCSSouthEastTail R dx dy)
      (hexCSSourceAbove_ne_nil R hR) hC
      (hexCSSouthEastTail_ne_nil R dx dy hS)
      (hexCSSourceAbove_head R hR)
      (hexCSSourceAbove_getLast R hR) hChead hjoin
      (hexCSSouthEastTail_getLast R dx dy hE)
    have hz := hexCSLowerPeriod_cyclicTurnSum_eq_zero
      e ts he hne hadm ⟨hc, hedge, hj⟩
    dsimp only at hz
    change ons_openTurnSum C + hexCSWindowExteriorTurn e = 0
    rw [hsplit, hexCSSourceAbove_openTurn R hR,
      hexCSSouthEastTail_openTurn R dx dy hS hE'] at hz
    simp [hexCSWindowExteriorTurn, hc, hedge]
    omega

private theorem hexCS_finalHeading_eq_canonical_of_window_turn
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge))
    (hperiod : ons_openTurnSum (hexCSBrickDirections 1 ts) +
      hexCSWindowExteriorTurn e = 0) :
    hexInfra_headAccum 1 ts = hexCSCanonicalHeading e := by
  have htel := hexCS_brick_open_telescope 1 ts hadm.1.1
  have hmod := hexCS_finalHeadingFin_eq_canonical
    e ts he hne hadm
  have hhead : hexInfra_headAccum 1 ts = 1 + ts.sum := by
    rw [hexInfra_headAccum_eq_add_sum]
  rw [hmod] at htel
  obtain hleft | hright | hupp | hlow :=
    hexCS_boundary_classification e he
  · rcases hleft with ⟨hc, hedge, _⟩
    by_cases hs : 0 ≤ hexAWTrans e.vtx.1
    · simp [hexCSCanonicalHeading, hexCSWindowExteriorTurn, hc, hedge, hs,
        hexCSHeadingFin_four_window, hexBrickTurnPotential] at htel hperiod ⊢
      omega
    · simp [hexCSCanonicalHeading, hexCSWindowExteriorTurn, hc, hedge, hs,
        hexCSHeadingFin_neg_two_window, hexBrickTurnPotential] at htel hperiod ⊢
      omega
  · rcases hright with ⟨hc, hedge, _⟩
    simp [hexCSCanonicalHeading, hexCSWindowExteriorTurn, hc, hedge,
      hexCSHeadingFin_one, hexBrickTurnPotential] at htel hperiod ⊢
    omega
  · rcases hupp with ⟨hc, hedge, _⟩
    simp [hexCSCanonicalHeading, hexCSWindowExteriorTurn, hc, hedge,
      hexCSHeadingFin_three_window, hexBrickTurnPotential] at htel hperiod ⊢
    omega
  · rcases hlow with ⟨hc, hedge, _⟩
    simp [hexCSCanonicalHeading, hexCSWindowExteriorTurn, hc, hedge,
      hexCSHeadingFin_neg_one_window, hexBrickTurnPotential] at htel hperiod ⊢
    omega



theorem hexCS_boundaryWindowLaw (T L : ℕ) (hT : 0 < T) :
    HexCSBoundaryWindowLaw T L hT := by
  intro e ts he hne hadm
  have hperiod := hexCS_boundaryBrickTurnLaw e ts he hne hadm
  have hheading := hexCS_finalHeading_eq_canonical_of_window_turn
    e ts he hne hadm hperiod
  refine ⟨hexCSCanonicalHeading e, ?_⟩
  rw [hheading]
  omega

end

end StatMech.Universality

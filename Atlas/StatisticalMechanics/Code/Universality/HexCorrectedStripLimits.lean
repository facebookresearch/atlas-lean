/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Universality.HexCorrectedStripAssembly

namespace StatMech.Universality

open Complex HexWalk Set
open scoped BigOperators

noncomputable section



theorem hexCSInStrip_mono {T T' L L' : ℕ}
    (hT : T ≤ T') (hL : L ≤ L') (c : HexAWCoord)
    (hc : hexCSInStrip T L c) :
    hexCSInStrip T' L' c := by
  unfold hexCSInStrip at hc ⊢
  omega

theorem hexCSVertexSet_mono {T T' L L' : ℕ}
    (hT : T ≤ T') (hL : L ≤ L') :
    hexCSVertexSet T L ⊆ hexCSVertexSet T' L' := by
  intro c hc
  rw [hexCS_mem_vertexSet_iff] at hc ⊢
  exact hexCSInStrip_mono hT hL c hc

theorem hexCSMids_mono {T T' L L' : ℕ}
    (hT : T ≤ T') (hL : L ≤ L') :
    hexCSMids T L ⊆ hexCSMids T' L' := by
  intro z hz
  rw [hexCSMids, Finset.mem_biUnion] at hz ⊢
  obtain ⟨v, _, hv⟩ := hz
  rw [Finset.mem_image] at hv
  obtain ⟨e, _, rfl⟩ := hv
  let v' : HexCSVertex T' L' :=
    ⟨v.1, hexCSVertexSet_mono hT hL v.2⟩
  refine ⟨v', Finset.mem_univ _, ?_⟩
  rw [Finset.mem_image]
  exact ⟨e, Finset.mem_univ _, rfl⟩

theorem hexCSFiniteRegion_mono
    {T T' L L' : ℕ} {hpos : 0 < T} {hpos' : 0 < T'}
    (hT : T ≤ T') (hL : L ≤ L') (z : ℂ)
    (hz : (hexCSFiniteRegion T L hpos).inRegion z) :
    (hexCSFiniteRegion T' L' hpos').inRegion z := by
  change z ∈ hexCSMids T L at hz
  change z ∈ hexCSMids T' L'
  exact hexCSMids_mono hT hL hz

theorem hexCSFiniteRegion_mono_L
    {T L L' : ℕ} {hpos : 0 < T} (hL : L ≤ L') (z : ℂ) :
    (hexCSFiniteRegion T L hpos).inRegion z →
      (hexCSFiniteRegion T L' hpos).inRegion z :=
  hexCSFiniteRegion_mono le_rfl hL z

theorem hexCSFiniteRegion_mono_T
    {T T' L : ℕ} {hpos : 0 < T} {hpos' : 0 < T'}
    (hT : T ≤ T') (z : ℂ) :
    (hexCSFiniteRegion T L hpos).inRegion z →
      (hexCSFiniteRegion T' L hpos').inRegion z :=
  hexCSFiniteRegion_mono hT le_rfl z



theorem endpointStaysIn_mono
    {region region' : ℂ → Prop} {a : ℂ} {h0 : ℤ} {ts : List ℤ}
    (hsub : ∀ z, region z → region' z)
    (hstay : (ofTurns a h0 ts).StaysIn region) :
    (ofTurns a h0 ts).StaysIn region' := by
  intro z hz
  exact hsub z (hstay z hz)

theorem endpointCountWeight_mono_region
    {region region' : ℂ → Prop} (a : ℂ) (h0 : ℤ) (z : ℂ)
    {x : ℝ} (hx : 0 ≤ x)
    (hsub : ∀ m, region m → region' m) (ts : List ℤ) :
    endpointCountWeight region a h0 z x ts ≤
      endpointCountWeight region' a h0 z x ts := by
  by_cases hguard :
      (ofTurns a h0 ts).EndpointIsLegalSAW ∧
        (ofTurns a h0 ts).StaysIn region ∧
        (ofTurns a h0 ts).EndsAt z
  · have hguard' :
        (ofTurns a h0 ts).EndpointIsLegalSAW ∧
          (ofTurns a h0 ts).StaysIn region' ∧
          (ofTurns a h0 ts).EndsAt z :=
      ⟨hguard.1, endpointStaysIn_mono hsub hguard.2.1, hguard.2.2⟩
    simp [endpointCountWeight, hguard, hguard']
  · rw [show endpointCountWeight region a h0 z x ts = 0 by
        simp [endpointCountWeight, hguard]]
    exact endpointCountWeight_nonneg region' a h0 z hx ts

theorem HexFiniteRegion.endpointCountWeight_summable
    (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ) (z : ℂ) (x : ℝ) :
    Summable (fun ts : List ℤ =>
      endpointCountWeight R.inRegion a h0 z x ts) := by
  let S := (hexFinite_boundedLegal_finite R.verts.card).toFinset
  apply summable_of_ne_finset_zero (s := S)
  intro ts hts
  by_contra hne
  apply hts
  change ts ∈ (hexFinite_boundedLegal_finite R.verts.card).toFinset
  rw [Set.Finite.mem_toFinset]
  have hguard :
      (ofTurns a h0 ts).EndpointIsLegalSAW ∧
        (ofTurns a h0 ts).StaysIn R.inRegion ∧
        (ofTurns a h0 ts).EndsAt z := by
    by_contra hfalse
    unfold endpointCountWeight at hne
    rw [if_neg hfalse] at hne
    exact hne rfl
  exact ⟨hguard.1.1,
    R.endpointLength_le a h0 ts hguard.1.2 hguard.2.1⟩

theorem endpointCountObservable_mono_finite
    (R R' : HexFiniteRegion) (a : ℂ) (h0 : ℤ) (z : ℂ)
    {x : ℝ} (hx : 0 ≤ x)
    (hsub : ∀ m, R.inRegion m → R'.inRegion m) :
    endpointCountObservable R.inRegion a h0 z x ≤
      endpointCountObservable R'.inRegion a h0 z x := by
  unfold endpointCountObservable
  exact (R.endpointCountWeight_summable a h0 z x).tsum_le_tsum
    (endpointCountWeight_mono_region a h0 z hx hsub)
    (R'.endpointCountWeight_summable a h0 z x)

theorem hexCS_endpointCountObservable_mono
    {T T' L L' : ℕ} {hpos : 0 < T} {hpos' : 0 < T'}
    (hT : T ≤ T') (hL : L ≤ L') (z : ℂ) :
    endpointCountObservable (hexCSFiniteRegion T L hpos).inRegion
        hexAWStart 1 z hexChi ≤
      endpointCountObservable (hexCSFiniteRegion T' L' hpos').inRegion
        hexAWStart 1 z hexChi := by
  apply endpointCountObservable_mono_finite
    (hexCSFiniteRegion T L hpos) (hexCSFiniteRegion T' L' hpos')
    hexAWStart 1 z hexChi_pos.le
  exact hexCSFiniteRegion_mono hT hL




def HexCSSideWalk (T L : ℕ) (hT : 0 < T) (ts : List ℤ) : Prop :=
  (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
    (ofTurns hexAWStart 1 ts).StaysIn
      (hexCSFiniteRegion T L hT).inRegion ∧
    ∃ c : HexAWCoord,
      c ∈ hexCSVertexSet T L ∧ c.color = .black ∧
        hexAWDepth c = 0 ∧
        hexAWMid c 0 ≠ hexAWStart ∧
        (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c 0)


def HexCSTopWalk (T L : ℕ) (hT : 0 < T) (ts : List ℤ) : Prop :=
  (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
    (ofTurns hexAWStart 1 ts).StaysIn
      (hexCSFiniteRegion T L hT).inRegion ∧
    ∃ c : HexAWCoord,
      c ∈ hexCSVertexSet T L ∧ c.color = .white ∧
        hexAWDepth c = T ∧
        (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c 0)


def HexCSSlantWalk (T L : ℕ) (hT : 0 < T) (ts : List ℤ) : Prop :=
  (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
    (ofTurns hexAWStart 1 ts).StaysIn
      (hexCSFiniteRegion T L hT).inRegion ∧
    ∃ c : HexAWCoord,
      c ∈ hexCSVertexSet T L ∧ c.color = .white ∧
        ((c.i = L ∧
            (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c 1)) ∨
          (c.j = L ∧
            (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c 2)))

theorem hexCSSideWalk_mono
    {T T' L L' : ℕ} {hpos : 0 < T} {hpos' : 0 < T'}
    (hT : T ≤ T') (hL : L ≤ L') {ts : List ℤ}
    (hwalk : HexCSSideWalk T L hpos ts) :
    HexCSSideWalk T' L' hpos' ts := by
  rcases hwalk with ⟨hlegal, hstay, c, hc, hcolor, hdepth, hne, hend⟩
  exact ⟨hlegal, endpointStaysIn_mono
      (hexCSFiniteRegion_mono hT hL) hstay,
    c, hexCSVertexSet_mono hT hL hc, hcolor, hdepth, hne, hend⟩

theorem hexCSTopWalk_mono_L
    {T L L' : ℕ} {hpos : 0 < T} (hL : L ≤ L') {ts : List ℤ}
    (hwalk : HexCSTopWalk T L hpos ts) :
    HexCSTopWalk T L' hpos ts := by
  rcases hwalk with ⟨hlegal, hstay, c, hc, hcolor, hdepth, hend⟩
  exact ⟨hlegal, endpointStaysIn_mono
      (hexCSFiniteRegion_mono le_rfl hL) hstay,
    c, hexCSVertexSet_mono le_rfl hL hc, hcolor, hdepth, hend⟩



def HexCSTopWalkAtWidth (T : ℕ) (hT : 0 < T) (ts : List ℤ) : Prop :=
  ∃ L : ℕ, HexCSTopWalk T L hT ts

theorem hexCSTopWalk_subset_atWidth
    (T L : ℕ) (hT : 0 < T) :
    ∀ ts, HexCSTopWalk T L hT ts → HexCSTopWalkAtWidth T hT ts := by
  intro ts hts
  exact ⟨L, hts⟩





noncomputable def hexCSTopWalkHeight
    {T : ℕ} {hT : 0 < T}
    (w : {ts : List ℤ // HexCSTopWalkAtWidth T hT ts}) : ℕ :=
  w.2.choose

theorem hexCSTopWalkHeight_spec
    {T : ℕ} {hT : 0 < T}
    (w : {ts : List ℤ // HexCSTopWalkAtWidth T hT ts}) :
    HexCSTopWalk T (hexCSTopWalkHeight w) hT w.1 :=
  w.2.choose_spec


noncomputable def hexCSTopFinsetHeight
    {T : ℕ} {hT : 0 < T}
    (s : Finset {ts : List ℤ // HexCSTopWalkAtWidth T hT ts}) : ℕ :=
  s.sup hexCSTopWalkHeight



theorem hexCSTopWalk_finset_fits
    {T : ℕ} {hT : 0 < T}
    (s : Finset {ts : List ℤ // HexCSTopWalkAtWidth T hT ts})
    (w : {ts : List ℤ // HexCSTopWalkAtWidth T hT ts})
    (hw : w ∈ s) :
    HexCSTopWalk T (hexCSTopFinsetHeight s) hT w.1 := by
  apply hexCSTopWalk_mono_L
    (Finset.le_sup (f := hexCSTopWalkHeight) hw)
  exact hexCSTopWalkHeight_spec w

theorem hexAWNeighbor_color_ne (c : HexAWCoord) (e : Fin 3) :
    (hexAWNeighbor c e).color ≠ c.color := by
  rcases c with ⟨i, j, color⟩
  cases color <;> fin_cases e <;> simp [hexAWNeighbor]



theorem hexAWMid_white_injective
    {c d : HexAWCoord} {e f : Fin 3}
    (hc : c.color = .white) (hd : d.color = .white)
    (hm : hexAWMid c e = hexAWMid d f) :
    c = d ∧ e = f := by
  rcases (hexAWMid_eq_iff c d e f).mp hm with
    ⟨hdc, hfe⟩ | ⟨hdc, hfe⟩
  · exact ⟨hdc.symm, hfe.symm⟩
  · exfalso
    apply hexAWNeighbor_color_ne c e
    calc
      (hexAWNeighbor c e).color = d.color :=
        congrArg HexAWCoord.color hdc.symm
      _ = .white := hd
      _ = c.color := hc.symm



theorem hexCSSlantWalk_height_unique
    {T L L' : ℕ} {hT : 0 < T} {ts : List ℤ}
    (hL : HexCSSlantWalk T L hT ts)
    (hL' : HexCSSlantWalk T L' hT ts) :
    L = L' := by
  rcases hL with ⟨_, _, c, _, hc, hside⟩
  rcases hL' with ⟨_, _, d, _, hd, hside'⟩
  rcases hside with ⟨hci, hend⟩ | ⟨hcj, hend⟩ <;>
    rcases hside' with ⟨hdi, hend'⟩ | ⟨hdj, hend'⟩
  · have hm : hexAWMid c 1 = hexAWMid d 1 := hend.symm.trans hend'
    obtain ⟨hcd, _⟩ := hexAWMid_white_injective hc hd hm
    rw [hcd] at hci
    omega
  · have hm : hexAWMid c 1 = hexAWMid d 2 := hend.symm.trans hend'
    have hedge := (hexAWMid_white_injective hc hd hm).2
    omega
  · have hm : hexAWMid c 2 = hexAWMid d 1 := hend.symm.trans hend'
    have hedge := (hexAWMid_white_injective hc hd hm).2
    omega
  · have hm : hexAWMid c 2 = hexAWMid d 2 := hend.symm.trans hend'
    obtain ⟨hcd, _⟩ := hexAWMid_white_injective hc hd hm
    rw [hcd] at hcj
    omega



def HexCSSlantWalkAtWidth (T : ℕ) (hT : 0 < T) (ts : List ℤ) : Prop :=
  ∃ L : ℕ, HexCSSlantWalk T L hT ts

noncomputable def hexCSSlantWalkHeight
    {T : ℕ} {hT : 0 < T}
    (w : {ts : List ℤ // HexCSSlantWalkAtWidth T hT ts}) : ℕ :=
  w.2.choose

theorem hexCSSlantWalkHeight_spec
    {T : ℕ} {hT : 0 < T}
    (w : {ts : List ℤ // HexCSSlantWalkAtWidth T hT ts}) :
    HexCSSlantWalk T (hexCSSlantWalkHeight w) hT w.1 :=
  w.2.choose_spec

theorem hexCSSlantWalkHeight_eq
    {T L : ℕ} {hT : 0 < T}
    (w : {ts : List ℤ // HexCSSlantWalkAtWidth T hT ts})
    (hw : HexCSSlantWalk T L hT w.1) :
    hexCSSlantWalkHeight w = L :=
  hexCSSlantWalk_height_unique (hexCSSlantWalkHeight_spec w) hw

end

end StatMech.Universality

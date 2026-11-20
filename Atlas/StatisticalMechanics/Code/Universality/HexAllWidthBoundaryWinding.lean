/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















import Code.Universality.HexAllWidthStripOrbits
import Code.Universality.HexEndpointVertex

namespace StatMech.Universality

open Complex HexWalk
open scoped BigOperators

noncomputable section




theorem hsc_genEndpointVertices (a : ℂ) (h0 : ℤ) (ts : List ℤ) :
    (ofTurns a h0 (hsc_negTurns ts)).endpointVertices =
      (ofTurns a h0 ts).endpointVertices.map (hsc_refl a h0) := by
  unfold endpointVertices vertices
  simp only [ofTurns_startMid, ofTurns_h0, ofTurns_turns]
  have hverts := hsc_genVerticesAux a h0 a h0 ts
  have hfix : hsc_refl a h0 a = a := hsc_refl_fixed a h0
  have hhead : 2 * h0 - h0 = h0 := by ring
  rw [hfix, hhead] at hverts
  rw [hverts]
  have map_dropLast (l : List ℂ) :
      (l.map (hsc_refl a h0)).dropLast =
        l.dropLast.map (hsc_refl a h0) := by
    induction l with
    | nil => simp
    | cons x xs =>
        cases xs with
        | nil => simp
        | cons y ys => simp_all
  exact map_dropLast _


theorem hsc_genEndpointIsSAW (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsaw : (ofTurns a h0 ts).EndpointIsSAW) :
    (ofTurns a h0 (hsc_negTurns ts)).EndpointIsSAW := by
  unfold EndpointIsSAW at *
  rw [hsc_genEndpointVertices]
  exact hsaw.map (hsc_refl_injective a h0)


theorem hsc_genEndpointIsLegalSAW (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlegal : (ofTurns a h0 ts).EndpointIsLegalSAW) :
    (ofTurns a h0 (hsc_negTurns ts)).EndpointIsLegalSAW :=
  ⟨hsc_genLegalTurns a h0 ts hlegal.1,
    hsc_genEndpointIsSAW a h0 ts hlegal.2⟩


@[simp] theorem hsc_genEndpointNumVertices (a : ℂ) (h0 : ℤ)
    (ts : List ℤ) :
    (ofTurns a h0 (hsc_negTurns ts)).endpointNumVertices =
      (ofTurns a h0 ts).endpointNumVertices := by
  simp [endpointNumVertices, hsc_negTurns]


theorem hsc_endpoint_admissible_refl_iff
    (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (hsym : ∀ m, region m → region (hsc_refl a h0 m)) (ts : List ℤ) :
    ((ofTurns a h0 (hsc_negTurns ts)).EndpointIsLegalSAW ∧
        (ofTurns a h0 (hsc_negTurns ts)).StaysIn region ∧
        (ofTurns a h0 (hsc_negTurns ts)).EndsAt (hsc_refl a h0 z)) ↔
      ((ofTurns a h0 ts).EndpointIsLegalSAW ∧
        (ofTurns a h0 ts).StaysIn region ∧
        (ofTurns a h0 ts).EndsAt z) := by
  constructor
  · rintro ⟨hlegal, hstay, hend⟩
    have hlegal' := hsc_genEndpointIsLegalSAW a h0 (hsc_negTurns ts) hlegal
    have hstay' := hsc_genStaysIn region a h0 (hsc_negTurns ts) hsym hstay
    refine ⟨?_, ?_, ?_⟩
    · rw [hsc_negTurns_negTurns] at hlegal'
      exact hlegal'
    · rw [hsc_negTurns_negTurns] at hstay'
      exact hstay'
    · unfold EndsAt at *
      rw [hsc_genEndMid] at hend
      exact hsc_refl_injective a h0 hend
  · rintro ⟨hlegal, hstay, hend⟩
    refine ⟨hsc_genEndpointIsLegalSAW a h0 ts hlegal,
      hsc_genStaysIn region a h0 ts hsym hstay, ?_⟩
    unfold EndsAt at *
    rw [hsc_genEndMid, hend]




noncomputable def endpointCountWeight (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (z : ℂ) (x : ℝ) (ts : List ℤ) : ℝ :=
  haveI := Classical.propDecidable
    ((ofTurns a h0 ts).EndpointIsLegalSAW ∧
      (ofTurns a h0 ts).StaysIn region ∧
      (ofTurns a h0 ts).EndsAt z)
  if (ofTurns a h0 ts).EndpointIsLegalSAW ∧
      (ofTurns a h0 ts).StaysIn region ∧
      (ofTurns a h0 ts).EndsAt z then
    x ^ (ofTurns a h0 ts).endpointNumVertices
  else 0


noncomputable def endpointCountObservable (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (z : ℂ) (x : ℝ) : ℝ :=
  ∑' ts : List ℤ, endpointCountWeight region a h0 z x ts

theorem endpointCountWeight_nonneg (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (z : ℂ) {x : ℝ} (hx : 0 ≤ x) (ts : List ℤ) :
    0 ≤ endpointCountWeight region a h0 z x ts := by
  unfold endpointCountWeight
  split <;> positivity


theorem endpointParafSummand_factor (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (z : ℂ) (σ x W : ℝ) (ts : List ℤ)
    (hdet : (ofTurns a h0 ts).EndpointIsLegalSAW ∧
        (ofTurns a h0 ts).StaysIn region ∧
        (ofTurns a h0 ts).EndsAt z →
      (ofTurns a h0 ts).turning = W) :
    endpointParafSummand region a h0 z σ x ts =
      Complex.exp (-Complex.I * (σ : ℂ) * (W : ℂ)) *
        ((endpointCountWeight region a h0 z x ts : ℝ) : ℂ) := by
  unfold endpointParafSummand endpointCountWeight
  split_ifs with h
  · rw [hdet h]
    push_cast
    ring
  · push_cast
    ring


theorem endpointParafObservable_factor (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (z : ℂ) (σ x W : ℝ)
    (hdet : ∀ ts,
      (ofTurns a h0 ts).EndpointIsLegalSAW ∧
          (ofTurns a h0 ts).StaysIn region ∧
          (ofTurns a h0 ts).EndsAt z →
        (ofTurns a h0 ts).turning = W) :
    endpointParafObservable region a h0 z σ x =
      Complex.exp (-Complex.I * (σ : ℂ) * (W : ℂ)) *
        ((endpointCountObservable region a h0 z x : ℝ) : ℂ) := by
  unfold endpointParafObservable endpointCountObservable
  rw [Complex.ofReal_tsum, ← tsum_mul_left]
  exact tsum_congr (fun ts =>
    endpointParafSummand_factor region a h0 z σ x W ts (hdet ts))


theorem endpointCountWeight_refl
    (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) (x : ℝ)
    (hsym : ∀ m, region m → region (hsc_refl a h0 m)) (ts : List ℤ) :
    endpointCountWeight region a h0 (hsc_refl a h0 z) x
        (hsc_negTurns ts) =
      endpointCountWeight region a h0 z x ts := by
  unfold endpointCountWeight
  have hiff := hsc_endpoint_admissible_refl_iff region a h0 z hsym ts
  by_cases h : (ofTurns a h0 ts).EndpointIsLegalSAW ∧
      (ofTurns a h0 ts).StaysIn region ∧
      (ofTurns a h0 ts).EndsAt z
  · rw [if_pos (hiff.mpr h), if_pos h, hsc_genEndpointNumVertices]
  · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h]


theorem endpointCountObservable_refl
    (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) (x : ℝ)
    (hsym : ∀ m, region m → region (hsc_refl a h0 m)) :
    endpointCountObservable region a h0 (hsc_refl a h0 z) x =
      endpointCountObservable region a h0 z x := by
  unfold endpointCountObservable
  rw [← Equiv.tsum_eq hsc_negEquiv
    (fun ts => endpointCountWeight region a h0 (hsc_refl a h0 z) x ts)]
  exact tsum_congr (endpointCountWeight_refl region a h0 z x hsym)



theorem endpoint_det_winding_reflect
    (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) (W : ℝ)
    (hsym : ∀ m, region m → region (hsc_refl a h0 m))
    (hdet : ∀ ts,
      (ofTurns a h0 ts).EndpointIsLegalSAW ∧
          (ofTurns a h0 ts).StaysIn region ∧
          (ofTurns a h0 ts).EndsAt z →
        (ofTurns a h0 ts).turning = W) :
    ∀ ts,
      (ofTurns a h0 ts).EndpointIsLegalSAW ∧
          (ofTurns a h0 ts).StaysIn region ∧
          (ofTurns a h0 ts).EndsAt (hsc_refl a h0 z) →
        (ofTurns a h0 ts).turning = -W := by
  intro ts hadm
  have href :
      (ofTurns a h0 (hsc_negTurns ts)).EndpointIsLegalSAW ∧
        (ofTurns a h0 (hsc_negTurns ts)).StaysIn region ∧
        (ofTurns a h0 (hsc_negTurns ts)).EndsAt z := by
    refine ⟨hsc_genEndpointIsLegalSAW a h0 ts hadm.1,
      hsc_genStaysIn region a h0 ts hsym hadm.2.1, ?_⟩
    unfold EndsAt at *
    rw [hsc_genEndMid, hadm.2.2, hsc_refl_invol]
  have hW := hdet (hsc_negTurns ts) href
  rw [hsc_genTurning_neg] at hW
  linarith




theorem hexAWNeighborPos_eq_mid_add (c : HexAWCoord) (e : Fin 3) :
    hexAWPos (hexAWNeighbor c e) =
      hexAWMid c e + halfStep (hexAWHeading c e) := by
  have hmid := hexAWMid_sub_pos c e
  have hpos := hexAWPos_neighbor c e
  calc
    hexAWPos (hexAWNeighbor c e) =
        hexAWPos c + hexUnit (hexAWHeading c e) := by
      linear_combination hpos
    _ = hexAWMid c e + (1 / 2 : ℂ) *
        hexUnit (hexAWHeading c e) := by
      have hmideq : hexAWMid c e = hexAWPos c +
          (1 / 2 : ℂ) * hexUnit (hexAWHeading c e) := by
        linear_combination hmid
      rw [hmideq]
      ring
    _ = hexAWMid c e + halfStep (hexAWHeading c e) := rfl



theorem hexAWEndpoint_finalHeading_mod
    {T L : ℕ} (e : HexAWIncidence T L) (ts : List ℤ)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt
      (hexAWMid e.vtx.1 e.edge))
    (hexit : hexInfra_midAccum hexAWStart 1 ts +
        halfStep (hexInfra_headAccum 1 ts) =
      hexAWPos (hexAWNeighbor e.vtx.1 e.edge)) :
    (6 : ℤ) ∣
      (hexInfra_headAccum 1 ts - hexAWHeading e.vtx.1 e.edge) := by
  apply hexInfra_finalHeading_mod_of_lastVertex hexAWStart 1
    (hexAWMid e.vtx.1 e.edge) (hexAWHeading e.vtx.1 e.edge) ts hend
  rwa [hexAWNeighborPos_eq_mid_add] at hexit



theorem hexAWEndpoint_finalHeading_eq_of_window
    {T L : ℕ} (e : HexAWIncidence T L) (ts : List ℤ) (w : ℤ)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt
      (hexAWMid e.vtx.1 e.edge))
    (hexit : hexInfra_midAccum hexAWStart 1 ts +
        halfStep (hexInfra_headAccum 1 ts) =
      hexAWPos (hexAWNeighbor e.vtx.1 e.edge))
    (hwalkL : w ≤ hexInfra_headAccum 1 ts)
    (hwalkU : hexInfra_headAccum 1 ts < w + 6)
    (hedgeL : w ≤ hexAWHeading e.vtx.1 e.edge)
    (hedgeU : hexAWHeading e.vtx.1 e.edge < w + 6) :
    hexInfra_headAccum 1 ts = hexAWHeading e.vtx.1 e.edge := by
  have hdvd := hexAWEndpoint_finalHeading_mod e ts hend hexit
  omega



theorem hexAWEndpoint_turning_eq_of_window
    {T L : ℕ} (e : HexAWIncidence T L) (ts : List ℤ) (w : ℤ)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt
      (hexAWMid e.vtx.1 e.edge))
    (hexit : hexInfra_midAccum hexAWStart 1 ts +
        halfStep (hexInfra_headAccum 1 ts) =
      hexAWPos (hexAWNeighbor e.vtx.1 e.edge))
    (hwalkL : w ≤ hexInfra_headAccum 1 ts)
    (hwalkU : hexInfra_headAccum 1 ts < w + 6)
    (hedgeL : w ≤ hexAWHeading e.vtx.1 e.edge)
    (hedgeU : hexAWHeading e.vtx.1 e.edge < w + 6) :
    (ofTurns hexAWStart 1 ts).turning =
      (Real.pi / 3) * ((hexAWHeading e.vtx.1 e.edge : ℝ) - 1) := by
  simpa only [Int.cast_one] using
    (hexInfra_turning_const_of_finalHeading hexAWStart 1 ts
      (hexAWHeading e.vtx.1 e.edge)
      (hexAWEndpoint_finalHeading_eq_of_window e ts w hend hexit
        hwalkL hwalkU hedgeL hedgeU))





def hexAWLowerSlantWitnessCoord (L : ℕ) : HexAWCoord :=
  ⟨-(L : ℤ) - 1, (L : ℤ), .black⟩


def hexAWUpperSlantWitnessCoord (L : ℕ) : HexAWCoord :=
  ⟨(L : ℤ), -(L : ℤ) - 1, .black⟩

@[simp] theorem hexAWLowerSlantWitnessCoord_mem (L : ℕ) :
    hexAWLowerSlantWitnessCoord L ∈ hexAWVertexSet 2 L := by
  rw [hexAW_mem_vertexSet_iff]
  simp [hexAWLowerSlantWitnessCoord, hexAWInStrip, hexAWBookRe2,
    hexAWBookSqrt3Im2, hexAWDepth, hexAWLong, hexAWTrans]
  omega

@[simp] theorem hexAWUpperSlantWitnessCoord_mem (L : ℕ) :
    hexAWUpperSlantWitnessCoord L ∈ hexAWVertexSet 2 L := by
  rw [hexAW_mem_vertexSet_iff]
  simp [hexAWUpperSlantWitnessCoord, hexAWInStrip, hexAWBookRe2,
    hexAWBookSqrt3Im2, hexAWDepth, hexAWLong, hexAWTrans]
  omega


def hexAWLowerSlantWitness (L : ℕ) : HexAWIncidence 2 L :=
  ⟨⟨hexAWLowerSlantWitnessCoord L,
      hexAWLowerSlantWitnessCoord_mem L⟩, 1⟩


def hexAWUpperSlantWitness (L : ℕ) : HexAWIncidence 2 L :=
  ⟨⟨hexAWUpperSlantWitnessCoord L,
      hexAWUpperSlantWitnessCoord_mem L⟩, 2⟩

@[simp] theorem hexAWLowerSlantWitness_heading (L : ℕ) :
    hexAWHeading (hexAWLowerSlantWitness L).vtx.1
      (hexAWLowerSlantWitness L).edge = 0 := rfl

@[simp] theorem hexAWUpperSlantWitness_heading (L : ℕ) :
    hexAWHeading (hexAWUpperSlantWitness L).vtx.1
      (hexAWUpperSlantWitness L).edge = 2 := rfl

theorem hexAWLowerSlantWitness_mem_boundary (L : ℕ) :
    hexAWLowerSlantWitness L ∈ hexAWBoundaryIncidences 2 L := by
  rw [hexAW_mem_boundary_iff]
  unfold hexAWIsInterior hexAWLowerSlantWitness
  rw [hexAW_mem_vertexSet_iff]
  simp [hexAWNeighbor, hexAWLowerSlantWitnessCoord, hexAWInStrip,
    hexAWBookRe2, hexAWBookSqrt3Im2, hexAWDepth, hexAWLong,
    hexAWTrans]
  omega

theorem hexAWUpperSlantWitness_mem_boundary (L : ℕ) :
    hexAWUpperSlantWitness L ∈ hexAWBoundaryIncidences 2 L := by
  rw [hexAW_mem_boundary_iff]
  unfold hexAWIsInterior hexAWUpperSlantWitness
  rw [hexAW_mem_vertexSet_iff]
  simp [hexAWNeighbor, hexAWUpperSlantWitnessCoord, hexAWInStrip,
    hexAWBookRe2, hexAWBookSqrt3Im2, hexAWDepth, hexAWLong,
    hexAWTrans]
  omega




theorem hexAWLowerSlant_turning_ne_source
    (L : ℕ) (ts : List ℤ)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt
      (hexAWMid (hexAWLowerSlantWitness L).vtx.1
        (hexAWLowerSlantWitness L).edge))
    (hexit : hexInfra_midAccum hexAWStart 1 ts +
        halfStep (hexInfra_headAccum 1 ts) =
      hexAWPos (hexAWNeighbor (hexAWLowerSlantWitness L).vtx.1
        (hexAWLowerSlantWitness L).edge)) :
    (ofTurns hexAWStart 1 ts).turning ≠ -(2 * Real.pi / 3) := by
  intro hturn
  have hdvd := hexAWEndpoint_finalHeading_mod
    (hexAWLowerSlantWitness L) ts hend hexit
  simp only [hexAWLowerSlantWitness_heading, sub_zero] at hdvd
  have hformula := hexInfra_turning_eq_headAccum_sub hexAWStart 1 ts
  have hhead : hexInfra_headAccum 1 ts = -1 := by
    rw [hturn] at hformula
    norm_num at hformula
    have hp := Real.pi_pos
    have hmul : Real.pi *
        ((hexInfra_headAccum 1 ts : ℝ) + 1) = 0 := by
      calc
        Real.pi * ((hexInfra_headAccum 1 ts : ℝ) + 1) =
            3 * ((Real.pi / 3) *
              ((hexInfra_headAccum 1 ts : ℝ) - 1) -
                (-(2 * Real.pi / 3))) := by ring
        _ = 0 := by rw [← hformula]; ring
    have hreal : (hexInfra_headAccum 1 ts : ℝ) + 1 = 0 :=
      (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hp)
    have hcast : (hexInfra_headAccum 1 ts : ℝ) = (-1 : ℝ) := by
      linarith
    exact_mod_cast hcast
  rw [hhead] at hdvd
  omega




theorem hexAWUpperSlant_turning_ne_source
    (L : ℕ) (ts : List ℤ)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt
      (hexAWMid (hexAWUpperSlantWitness L).vtx.1
        (hexAWUpperSlantWitness L).edge))
    (hexit : hexInfra_midAccum hexAWStart 1 ts +
        halfStep (hexInfra_headAccum 1 ts) =
      hexAWPos (hexAWNeighbor (hexAWUpperSlantWitness L).vtx.1
        (hexAWUpperSlantWitness L).edge)) :
    (ofTurns hexAWStart 1 ts).turning ≠ 2 * Real.pi / 3 := by
  intro hturn
  have hdvd := hexAWEndpoint_finalHeading_mod
    (hexAWUpperSlantWitness L) ts hend hexit
  simp only [hexAWUpperSlantWitness_heading] at hdvd
  have hformula := hexInfra_turning_eq_headAccum_sub hexAWStart 1 ts
  have hhead : hexInfra_headAccum 1 ts = 3 := by
    rw [hturn] at hformula
    norm_num at hformula
    have hp := Real.pi_pos
    have hmul : Real.pi *
        ((hexInfra_headAccum 1 ts : ℝ) - 3) = 0 := by
      calc
        Real.pi * ((hexInfra_headAccum 1 ts : ℝ) - 3) =
            3 * ((Real.pi / 3) *
              ((hexInfra_headAccum 1 ts : ℝ) - 1) -
                (2 * Real.pi / 3)) := by ring
        _ = 0 := by rw [← hformula]; ring
    have hreal : (hexInfra_headAccum 1 ts : ℝ) - 3 = 0 :=
      (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hp)
    have hcast : (hexInfra_headAccum 1 ts : ℝ) = (3 : ℝ) := by
      linarith
    exact_mod_cast hcast
  rw [hhead] at hdvd
  omega

end

end StatMech.Universality

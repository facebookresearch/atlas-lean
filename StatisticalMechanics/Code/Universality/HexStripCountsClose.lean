/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































































import Mathlib
import Code.Universality.HexLattice
import Code.Universality.HexInfraDisplacement
import Code.Universality.HexInfraWinding
import Code.Universality.HexConnClosed

namespace StatMech.Universality

open HexWalk List Complex
open scoped BigOperators Real










def hsc_negTurns (ts : List ℤ) : List ℤ := ts.map (fun t => -t)

@[simp] theorem hsc_negTurns_nil : hsc_negTurns [] = [] := rfl
@[simp] theorem hsc_negTurns_cons (t : ℤ) (ts : List ℤ) :
    hsc_negTurns (t :: ts) = (-t) :: hsc_negTurns ts := rfl

@[simp] theorem hsc_negTurns_length (ts : List ℤ) :
    (hsc_negTurns ts).length = ts.length := by simp [hsc_negTurns]


theorem hsc_negTurns_negTurns (ts : List ℤ) : hsc_negTurns (hsc_negTurns ts) = ts := by
  simp [hsc_negTurns, List.map_map]








noncomputable def hsc_refl (a0 : ℂ) (h0 : ℤ) (z : ℂ) : ℂ :=
  a0 + (hexUnit h0)^2 * (starRingEnd ℂ) (z - a0)


theorem hsc_refl_fixed (a0 : ℂ) (h0 : ℤ) : hsc_refl a0 h0 a0 = a0 := by
  unfold hsc_refl; simp


theorem hsc_refl_invol (a0 : ℂ) (h0 : ℤ) (z : ℂ) :
    hsc_refl a0 h0 (hsc_refl a0 h0 z) = z := by
  unfold hsc_refl
  have hu : hexUnit h0 * (starRingEnd ℂ) (hexUnit h0) = 1 := by
    rw [Complex.mul_conj]
    have hns : Complex.normSq (hexUnit h0) = 1 := by
      rw [Complex.normSq_eq_norm_sq, norm_hexUnit]; norm_num
    rw [hns]; norm_num
  rw [show a0 + (hexUnit h0)^2 * (starRingEnd ℂ) (z - a0) - a0
        = (hexUnit h0)^2 * (starRingEnd ℂ) (z - a0) by ring]
  rw [map_mul, Complex.conj_conj]
  have key : (hexUnit h0)^2 * ((starRingEnd ℂ) ((hexUnit h0)^2) * (z - a0)) = z - a0 := by
    rw [map_pow]
    calc (hexUnit h0)^2 * (((starRingEnd ℂ) (hexUnit h0))^2 * (z - a0))
        = (hexUnit h0 * (starRingEnd ℂ) (hexUnit h0))^2 * (z - a0) := by ring
      _ = (1 : ℂ)^2 * (z - a0) := by rw [hu]
      _ = z - a0 := by ring
  rw [key]; ring


theorem hsc_refl_injective (a0 : ℂ) (h0 : ℤ) : Function.Injective (hsc_refl a0 h0) := by
  intro x y hxy
  unfold hsc_refl at hxy
  have hu : (hexUnit h0)^2 ≠ 0 := pow_ne_zero _ (hexUnit_ne_zero h0)
  have h1 : (hexUnit h0)^2 * (starRingEnd ℂ) (x - a0)
      = (hexUnit h0)^2 * (starRingEnd ℂ) (y - a0) := add_left_cancel hxy
  have h2 : (starRingEnd ℂ) (x - a0) = (starRingEnd ℂ) (y - a0) := mul_left_cancel₀ hu h1
  exact sub_left_injective ((starRingEnd ℂ).injective h2)








theorem hsc_conj_hexUnit (h : ℤ) :
    (starRingEnd ℂ) (hexUnit h) = hexUnit (-1 - h) := by
  unfold hexUnit
  rw [show Complex.I * ((Real.pi : ℂ) / 6 + ((h : ℝ) : ℂ) * ((Real.pi : ℂ) / 3))
        = ((Real.pi / 6 + (h : ℝ) * (Real.pi / 3) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      ← Complex.exp_conj]
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast; ring



theorem hsc_genHexUnit (h0 h : ℤ) :
    hexUnit (2 * h0 - h) = (hexUnit h0)^2 * (starRingEnd ℂ) (hexUnit h) := by
  rw [hsc_conj_hexUnit]
  unfold hexUnit
  rw [sq, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast; ring



theorem hsc_genHalfStep (h0 h : ℤ) :
    HexWalk.halfStep (2 * h0 - h) = (hexUnit h0)^2 * (starRingEnd ℂ) (HexWalk.halfStep h) := by
  unfold HexWalk.halfStep
  rw [map_mul, map_div₀, map_one, map_ofNat, hsc_genHexUnit]
  ring








theorem hsc_genHeadAccum (h0 h : ℤ) (ts : List ℤ) :
    hexInfra_headAccum (2 * h0 - h) (hsc_negTurns ts) = 2 * h0 - hexInfra_headAccum h ts := by
  induction ts generalizing h with
  | nil => simp
  | cons t ts ih =>
    rw [hsc_negTurns_cons, hexInfra_headAccum_cons, hexInfra_headAccum_cons]
    rw [show 2 * h0 - h + -t = 2 * h0 - (h + t) by ring]
    exact ih (h + t)



theorem hsc_genMidAccum (a0 : ℂ) (h0 : ℤ) (m : ℂ) (h : ℤ) (ts : List ℤ) :
    hexInfra_midAccum (hsc_refl a0 h0 m) (2 * h0 - h) (hsc_negTurns ts)
      = hsc_refl a0 h0 (hexInfra_midAccum m h ts) := by
  induction ts generalizing m h with
  | nil => simp
  | cons t ts ih =>
    rw [hsc_negTurns_cons, hexInfra_midAccum_cons, hexInfra_midAccum_cons]
    rw [show 2 * h0 - h + -t = 2 * h0 - (h + t) by ring]
    rw [show (hsc_refl a0 h0 m + HexWalk.halfStep (2 * h0 - h)
              + HexWalk.halfStep (2 * h0 - (h + t)))
          = hsc_refl a0 h0 (m + HexWalk.halfStep h + HexWalk.halfStep (h + t)) by
      unfold hsc_refl
      rw [hsc_genHalfStep, hsc_genHalfStep]
      rw [show m + HexWalk.halfStep h + HexWalk.halfStep (h + t) - a0
            = (m - a0) + HexWalk.halfStep h + HexWalk.halfStep (h + t) by ring,
          map_add, map_add]
      ring]
    exact ih (m + HexWalk.halfStep h + HexWalk.halfStep (h + t)) (h + t)



theorem hsc_genMidsAux (a0 : ℂ) (h0 : ℤ) (m : ℂ) (h : ℤ) (ts : List ℤ) :
    HexWalk.midsAux (hsc_refl a0 h0 m) (2 * h0 - h) (hsc_negTurns ts)
      = (HexWalk.midsAux m h ts).map (hsc_refl a0 h0) := by
  induction ts generalizing m h with
  | nil => simp
  | cons t ts ih =>
    rw [hsc_negTurns_cons, HexWalk.midsAux_cons, HexWalk.midsAux_cons, List.map_cons]
    rw [show 2 * h0 - h + -t = 2 * h0 - (h + t) by ring]
    congr 1
    rw [show (hsc_refl a0 h0 m + HexWalk.halfStep (2 * h0 - h)
            + HexWalk.halfStep (2 * h0 - (h + t)))
          = hsc_refl a0 h0 (m + HexWalk.halfStep h + HexWalk.halfStep (h + t)) by
      unfold hsc_refl
      rw [hsc_genHalfStep, hsc_genHalfStep]
      rw [show m + HexWalk.halfStep h + HexWalk.halfStep (h + t) - a0
            = (m - a0) + HexWalk.halfStep h + HexWalk.halfStep (h + t) by ring,
          map_add, map_add]
      ring]
    exact ih (m + HexWalk.halfStep h + HexWalk.halfStep (h + t)) (h + t)



theorem hsc_genVerticesAux (a0 : ℂ) (h0 : ℤ) (m : ℂ) (h : ℤ) (ts : List ℤ) :
    HexWalk.verticesAux (hsc_refl a0 h0 m) (2 * h0 - h) (hsc_negTurns ts)
      = (HexWalk.verticesAux m h ts).map (hsc_refl a0 h0) := by
  induction ts generalizing m h with
  | nil =>
    simp only [hsc_negTurns_nil, HexWalk.verticesAux_nil, List.map_cons, List.map_nil]
    congr 1
    unfold hsc_refl
    rw [hsc_genHalfStep]
    rw [show m + HexWalk.halfStep h - a0 = (m - a0) + HexWalk.halfStep h by ring, map_add]
    ring
  | cons t ts ih =>
    rw [hsc_negTurns_cons, HexWalk.verticesAux_cons, HexWalk.verticesAux_cons, List.map_cons]
    rw [show 2 * h0 - h + -t = 2 * h0 - (h + t) by ring]
    congr 1
    · unfold hsc_refl
      rw [hsc_genHalfStep]
      rw [show m + HexWalk.halfStep h - a0 = (m - a0) + HexWalk.halfStep h by ring, map_add]
      ring
    · rw [show (hsc_refl a0 h0 m + HexWalk.halfStep (2 * h0 - h)
              + HexWalk.halfStep (2 * h0 - (h + t)))
            = hsc_refl a0 h0 (m + HexWalk.halfStep h + HexWalk.halfStep (h + t)) by
        unfold hsc_refl
        rw [hsc_genHalfStep, hsc_genHalfStep]
        rw [show m + HexWalk.halfStep h + HexWalk.halfStep (h + t) - a0
              = (m - a0) + HexWalk.halfStep h + HexWalk.halfStep (h + t) by ring,
            map_add, map_add]
        ring]
      exact ih (m + HexWalk.halfStep h + HexWalk.halfStep (h + t)) (h + t)









theorem hsc_genEndMid (a : ℂ) (h0 : ℤ) (ts : List ℤ) :
    (HexWalk.ofTurns a h0 (hsc_negTurns ts)).endMid
      = hsc_refl a h0 ((HexWalk.ofTurns a h0 ts).endMid) := by
  rw [hexInfra_endMid_eq_midAccum, hexInfra_endMid_eq_midAccum]
  have h1 : hsc_refl a h0 a = a := hsc_refl_fixed a h0
  have h2 : (2 : ℤ) * h0 - h0 = h0 := by ring
  calc hexInfra_midAccum a h0 (hsc_negTurns ts)
      = hexInfra_midAccum (hsc_refl a h0 a) (2 * h0 - h0) (hsc_negTurns ts) := by rw [h1, h2]
    _ = hsc_refl a h0 (hexInfra_midAccum a h0 ts) := hsc_genMidAccum a h0 a h0 ts



theorem hsc_genIsSAW (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsaw : (HexWalk.ofTurns a h0 ts).IsSAW) :
    (HexWalk.ofTurns a h0 (hsc_negTurns ts)).IsSAW := by
  unfold HexWalk.IsSAW HexWalk.vertices at *
  simp only [HexWalk.ofTurns_startMid, HexWalk.ofTurns_h0, HexWalk.ofTurns_turns] at *
  have h2 : (2 : ℤ) * h0 - h0 = h0 := by ring
  have h1 : hsc_refl a h0 a = a := hsc_refl_fixed a h0
  rw [show HexWalk.verticesAux a h0 (hsc_negTurns ts)
        = HexWalk.verticesAux (hsc_refl a h0 a) (2 * h0 - h0) (hsc_negTurns ts) by rw [h1, h2]]
  rw [hsc_genVerticesAux]
  exact hsaw.map (hsc_refl_injective a h0)


theorem hsc_genLegalTurns (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlt : (HexWalk.ofTurns a h0 ts).LegalTurns) :
    (HexWalk.ofTurns a h0 (hsc_negTurns ts)).LegalTurns := by
  unfold HexWalk.LegalTurns at *
  simp only [HexWalk.ofTurns_turns, hsc_negTurns] at *
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  rcases hlt s hs with h | h
  · right; rw [h]
  · left; rw [h]; ring





theorem hsc_genStaysIn (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsym : ∀ m, region m → region (hsc_refl a h0 m))
    (hstays : (HexWalk.ofTurns a h0 ts).StaysIn region) :
    (HexWalk.ofTurns a h0 (hsc_negTurns ts)).StaysIn region := by
  unfold HexWalk.StaysIn HexWalk.mids at *
  simp only [HexWalk.ofTurns_startMid, HexWalk.ofTurns_h0, HexWalk.ofTurns_turns] at *
  intro mm hmm
  have h2 : (2 : ℤ) * h0 - h0 = h0 := by ring
  have h1 : hsc_refl a h0 a = a := hsc_refl_fixed a h0
  have hmids : HexWalk.midsAux a h0 (hsc_negTurns ts)
      = (HexWalk.midsAux a h0 ts).map (hsc_refl a h0) := by
    have := hsc_genMidsAux a h0 a h0 ts
    rwa [h1, h2] at this
  rw [hmids, List.mem_map] at hmm
  obtain ⟨m0, hm0, rfl⟩ := hmm
  exact hsym m0 (hstays m0 hm0)


theorem hsc_genNumVertices (a : ℂ) (h0 : ℤ) (ts : List ℤ) :
    (HexWalk.ofTurns a h0 (hsc_negTurns ts)).numVertices
      = (HexWalk.ofTurns a h0 ts).numVertices := by
  simp [HexWalk.numVertices, hsc_negTurns]


theorem hsc_genTurning_neg (a : ℂ) (h0 : ℤ) (ts : List ℤ) :
    (HexWalk.ofTurns a h0 (hsc_negTurns ts)).turning
      = -(HexWalk.ofTurns a h0 ts).turning := by
  simp only [HexWalk.turning_eq, HexWalk.ofTurns_turns, hsc_negTurns]
  have hsum : (List.map (fun t => -t) ts).sum = - ts.sum := by
    induction ts with
    | nil => simp
    | cons t ts ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [hsum]; push_cast; ring










def hsc_negEquiv : List ℤ ≃ List ℤ where
  toFun := hsc_negTurns
  invFun := hsc_negTurns
  left_inv := hsc_negTurns_negTurns
  right_inv := hsc_negTurns_negTurns





theorem hsc_cw_refl (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) (x : ℝ)
    (hsym : ∀ m, region m → region (hsc_refl a h0 m)) (ts : List ℤ) :
    hexClosed_cw region a h0 (hsc_refl a h0 z) x (hsc_negTurns ts)
      = hexClosed_cw region a h0 z x ts := by
  unfold hexClosed_cw
  have hnum : (HexWalk.ofTurns a h0 (hsc_negTurns ts)).numVertices
      = (HexWalk.ofTurns a h0 ts).numVertices := hsc_genNumVertices a h0 ts
  have hiff : ((HexWalk.ofTurns a h0 (hsc_negTurns ts)).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 (hsc_negTurns ts)).StaysIn region
        ∧ (HexWalk.ofTurns a h0 (hsc_negTurns ts)).EndsAt (hsc_refl a h0 z))
      ↔ ((HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn region
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) := by
    constructor
    · rintro ⟨⟨hlt, hsaw⟩, hstays, hends⟩
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · have := hsc_genLegalTurns a h0 (hsc_negTurns ts) hlt
        rwa [hsc_negTurns_negTurns] at this
      · have := hsc_genIsSAW a h0 (hsc_negTurns ts) hsaw
        rwa [hsc_negTurns_negTurns] at this
      · have := hsc_genStaysIn region a h0 (hsc_negTurns ts) hsym hstays
        rwa [hsc_negTurns_negTurns] at this
      · unfold HexWalk.EndsAt at *
        rw [hsc_genEndMid] at hends
        exact hsc_refl_injective a h0 hends
    · rintro ⟨⟨hlt, hsaw⟩, hstays, hends⟩
      refine ⟨⟨hsc_genLegalTurns a h0 ts hlt, hsc_genIsSAW a h0 ts hsaw⟩,
        hsc_genStaysIn region a h0 ts hsym hstays, ?_⟩
      unfold HexWalk.EndsAt at *
      rw [hsc_genEndMid, hends]
  by_cases h : (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn region
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt z
  · rw [if_pos (hiff.mpr h), if_pos h, hnum]
  · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h]












theorem hsc_countObs_refl (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) (x : ℝ)
    (hsym : ∀ m, region m → region (hsc_refl a h0 m)) :
    hexClosed_countObs region a h0 (hsc_refl a h0 z) x
      = hexClosed_countObs region a h0 z x := by
  unfold hexClosed_countObs
  rw [← Equiv.tsum_eq hsc_negEquiv (fun ts => hexClosed_cw region a h0 (hsc_refl a h0 z) x ts)]
  exact tsum_congr (fun ts => hsc_cw_refl region a h0 z x hsym ts)















theorem hsc_detb_of_dett (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) (W : ℝ)
    (hsym : ∀ m, region m → region (hsc_refl a h0 m))
    (hdett : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn region
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt z → (HexWalk.ofTurns a h0 ts).turning = W) :
    ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn region
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt (hsc_refl a h0 z)
          → (HexWalk.ofTurns a h0 ts).turning = -W := by
  rintro ts ⟨⟨hlt, hsaw⟩, hstays, hends⟩
  have hlt' : (HexWalk.ofTurns a h0 (hsc_negTurns ts)).LegalTurns := hsc_genLegalTurns a h0 ts hlt
  have hsaw' : (HexWalk.ofTurns a h0 (hsc_negTurns ts)).IsSAW := hsc_genIsSAW a h0 ts hsaw
  have hstays' : (HexWalk.ofTurns a h0 (hsc_negTurns ts)).StaysIn region :=
    hsc_genStaysIn region a h0 ts hsym hstays
  have hends' : (HexWalk.ofTurns a h0 (hsc_negTurns ts)).EndsAt z := by
    unfold HexWalk.EndsAt at hends ⊢
    rw [hsc_genEndMid, hends, hsc_refl_invol]
  have hW := hdett (hsc_negTurns ts) ⟨⟨hlt', hsaw'⟩, hstays', hends'⟩
  rw [hsc_genTurning_neg] at hW
  linarith

























theorem hsc_sidePhaseLock_single (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (σ x W : ℝ)
    (hsym : ∀ m, region m → region (hsc_refl a h0 m))
    (hdett : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn region
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt z → (HexWalk.ofTurns a h0 ts).turning = W) :
    parafObservable region a h0 z σ x
        + parafObservable region a h0 (hsc_refl a h0 z) σ x
      = ((2 * Real.cos (σ * W) * hexClosed_countObs region a h0 z x : ℝ) : ℂ) :=
  hexClosed_sidePhaseLock_of_reflection region a h0 z (hsc_refl a h0 z) σ x W
    (hexClosed_countObs region a h0 z x) hdett
    (hsc_detb_of_dett region a h0 z W hsym hdett) rfl
    (hsc_countObs_refl region a h0 z x hsym)









theorem hsc_full_region_sym (a : ℂ) (h0 : ℤ) :
    ∀ m, (fun _ : ℂ => True) m → (fun _ : ℂ => True) (hsc_refl a h0 m) :=
  fun _ _ => trivial




theorem hsc_countObs_refl_full (a : ℂ) (h0 : ℤ) (z : ℂ) (x : ℝ) :
    hexClosed_countObs (fun _ => True) a h0 (hsc_refl a h0 z) x
      = hexClosed_countObs (fun _ => True) a h0 z x :=
  hsc_countObs_refl (fun _ => True) a h0 z x (hsc_full_region_sym a h0)






theorem hsc_sidePhaseLock_zeroWinding (a : ℂ) (h0 : ℤ) (z : ℂ) (σ x : ℝ)
    (hdet0 : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn (fun _ => True)
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt z → (HexWalk.ofTurns a h0 ts).turning = 0) :
    parafObservable (fun _ => True) a h0 z σ x
        + parafObservable (fun _ => True) a h0 (hsc_refl a h0 z) σ x
      = ((2 * hexClosed_countObs (fun _ => True) a h0 z x : ℝ) : ℂ) := by
  have h := hsc_sidePhaseLock_single (fun _ => True) a h0 z σ x 0 (hsc_full_region_sym a h0) hdet0
  rw [mul_zero, Real.cos_zero] at h
  rw [h]; push_cast; ring

end StatMech.Universality

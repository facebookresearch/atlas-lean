/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































































import Mathlib
import Code.Universality.HexConnFinal
import Code.Universality.HexInjections
import Code.Universality.HexBoundaryPhases

namespace StatMech.Universality

open Complex HexWalk Filter Topology
open scoped Topology Real BigOperators














noncomputable def hexClosed_cw (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (x : ℝ) (ts : List ℤ) : ℝ :=
  haveI := Classical.propDecidable ((ofTurns a h0 ts).IsLegalSAW
      ∧ (ofTurns a h0 ts).StaysIn inRegion ∧ (ofTurns a h0 ts).EndsAt z)
  if (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn inRegion
        ∧ (ofTurns a h0 ts).EndsAt z then x ^ (ofTurns a h0 ts).numVertices else 0




noncomputable def hexClosed_countObs (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (x : ℝ) : ℝ :=
  ∑' ts, hexClosed_cw inRegion a h0 z x ts


theorem hexClosed_cw_nonneg (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    {x : ℝ} (hx : 0 ≤ x) (ts : List ℤ) : 0 ≤ hexClosed_cw inRegion a h0 z x ts := by
  unfold hexClosed_cw; split <;> positivity












theorem hexClosed_parafSummand_factor (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (σ x W : ℝ) (ts : List ℤ)
    (hdet : (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn inRegion
        ∧ (ofTurns a h0 ts).EndsAt z → (ofTurns a h0 ts).turning = W) :
    parafSummand inRegion a h0 z σ x ts
      = Complex.exp (-Complex.I * (σ : ℂ) * (W : ℂ))
          * ((hexClosed_cw inRegion a h0 z x ts : ℝ) : ℂ) := by
  unfold parafSummand hexClosed_cw
  split_ifs with h
  · rw [hdet h]; push_cast; ring
  · push_cast; ring










theorem hexClosed_parafObservable_factor (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (σ x W : ℝ)
    (hdet : ∀ ts, (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn inRegion
        ∧ (ofTurns a h0 ts).EndsAt z → (ofTurns a h0 ts).turning = W) :
    parafObservable inRegion a h0 z σ x
      = Complex.exp (-Complex.I * (σ : ℂ) * (W : ℂ))
          * ((hexClosed_countObs inRegion a h0 z x : ℝ) : ℂ) := by
  unfold parafObservable hexClosed_countObs
  rw [Complex.ofReal_tsum, ← tsum_mul_left]
  exact tsum_congr (fun ts => hexClosed_parafSummand_factor inRegion a h0 z σ x W ts (hdet ts))
























theorem hexClosed_sidePhaseLock_of_reflection (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (zt zb : ℂ) (σ x W r : ℝ)
    (hdett : ∀ ts, (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn inRegion
        ∧ (ofTurns a h0 ts).EndsAt zt → (ofTurns a h0 ts).turning = W)
    (hdetb : ∀ ts, (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn inRegion
        ∧ (ofTurns a h0 ts).EndsAt zb → (ofTurns a h0 ts).turning = -W)
    (hreflt : hexClosed_countObs inRegion a h0 zt x = r)
    (hreflb : hexClosed_countObs inRegion a h0 zb x = r) :
    parafObservable inRegion a h0 zt σ x + parafObservable inRegion a h0 zb σ x
      = ((2 * Real.cos (σ * W) * r : ℝ) : ℂ) := by
  rw [hexClosed_parafObservable_factor inRegion a h0 zt σ x W hdett,
      hexClosed_parafObservable_factor inRegion a h0 zb σ x (-W) hdetb,
      hreflt, hreflb]
  
  have hkey : Complex.exp (-Complex.I * (σ : ℂ) * (W : ℂ))
        + Complex.exp (-Complex.I * (σ : ℂ) * ((-W : ℝ) : ℂ))
      = ((2 * Real.cos (σ * W) : ℝ) : ℂ) := by
    
    
    have h1 : -Complex.I * (σ : ℂ) * (W : ℂ) = ((-(σ * W) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    have h2 : -Complex.I * (σ : ℂ) * ((-W : ℝ) : ℂ) = ((σ * W : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h1, h2, add_comm]
    
    rw [hexExpI_add_neg (σ * W)]; push_cast; ring
  calc Complex.exp (-Complex.I * (σ : ℂ) * (W : ℂ)) * ((r : ℝ) : ℂ)
        + Complex.exp (-Complex.I * (σ : ℂ) * ((-W : ℝ) : ℂ)) * ((r : ℝ) : ℂ)
      = (Complex.exp (-Complex.I * (σ : ℂ) * (W : ℂ))
          + Complex.exp (-Complex.I * (σ : ℂ) * ((-W : ℝ) : ℂ))) * ((r : ℝ) : ℂ) := by ring
    _ = ((2 * Real.cos (σ * W) : ℝ) : ℂ) * ((r : ℝ) : ℂ) := by rw [hkey]
    _ = ((2 * Real.cos (σ * W) * r : ℝ) : ℂ) := by push_cast; ring












theorem hexClosed_cos_sigmaPi_eq_neg_cl :
    Real.cos ((5 / 8 : ℝ) * Real.pi) = -hexBdryCl := by
  rw [hexPhase_cl_from_turning, neg_neg, show (5 / 8 : ℝ) * Real.pi = 5 * Real.pi / 8 by ring]






















theorem hexClosed_term_le_colSum (a : ℂ) (h0 : ℤ) (T : ℕ) (χ : ℝ)
    (mem : List ℤ → Prop) (hreach hsummable hle_one) {x : ℝ} (hx : 0 ≤ x)
    (b : List ℤ) (hb : mem b)
    (hxsum : Summable (fun w : {ts // mem ts} =>
      x ^ (HexWalk.ofTurns a h0 w.1).numVertices)) :
    x ^ (HexWalk.ofTurns a h0 b).numVertices
      ≤ (hexColumnOfWidth a h0 T χ mem hreach hsummable hle_one).colSum x := by
  rw [hexColumnOfWidth_colSum]
  exact Summable.le_tsum hxsum ⟨b, hb⟩ (fun w _ => by positivity)


























theorem hexClosed_topSidePhase_eq (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (zt zb : ℂ) (σ x W r coeff cval θ : ℝ)
    (hdett : ∀ ts, (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn inRegion
        ∧ (ofTurns a h0 ts).EndsAt zt → (ofTurns a h0 ts).turning = W)
    (hdetb : ∀ ts, (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn inRegion
        ∧ (ofTurns a h0 ts).EndsAt zb → (ofTurns a h0 ts).turning = -W)
    (hreflt : hexClosed_countObs inRegion a h0 zt x = r)
    (hreflb : hexClosed_countObs inRegion a h0 zb x = r)
    (hcoeff : Real.cos (σ * W) = coeff) (hval : r = cval) (htilt : θ = 0) :
    parafObservable inRegion a h0 zt σ x + parafObservable inRegion a h0 zb σ x
      = 2 * Complex.exp ((θ : ℝ) * Complex.I) * ((coeff * cval : ℝ) : ℂ) := by
  rw [hexClosed_sidePhaseLock_of_reflection inRegion a h0 zt zb σ x W r
        hdett hdetb hreflt hreflb, htilt]
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [hcoeff, hval]; push_cast; ring












theorem hexClosed_colDomination (a : ℂ) (h0 : ℤ) (T : ℕ) (χ : ℝ)
    (mem : List ℤ → Prop) (hreach hsummable hle_one) {x : ℝ}
    (hx0 : 0 ≤ x) (hχ : 0 < χ) (hxχ : x ≤ χ)
    (b : List ℤ) (hb : mem b) :
    x ^ (HexWalk.ofTurns a h0 b).numVertices
      ≤ (hexColumnOfWidth a h0 T χ mem hreach hsummable hle_one).colSum x :=
  hexClosed_term_le_colSum a h0 T χ mem hreach hsummable hle_one hx0 b hb
    ((hexColumnOfWidth a h0 T χ mem hreach hsummable hle_one).colSum_summable hx0 hχ hxχ)











theorem hexClosed_factor_at_zero (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) (σ x : ℝ)
    (hdet : ∀ ts, (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn inRegion
        ∧ (ofTurns a h0 ts).EndsAt z → (ofTurns a h0 ts).turning = 0) :
    parafObservable inRegion a h0 z σ x
      = ((hexClosed_countObs inRegion a h0 z x : ℝ) : ℂ) := by
  rw [hexClosed_parafObservable_factor inRegion a h0 z σ x 0 hdet]
  simp




theorem hexClosed_term_le_colSum_trivial (a : ℂ) (h0 : ℤ) (T : ℕ) (χ : ℝ)
    (mem : List ℤ → Prop) (hreach hsummable hle_one) {x : ℝ} (hx : 0 ≤ x)
    (hb : mem ([] : List ℤ))
    (hxsum : Summable (fun w : {ts // mem ts} =>
      x ^ (HexWalk.ofTurns a h0 w.1).numVertices)) :
    x ^ (HexWalk.ofTurns a h0 ([] : List ℤ)).numVertices
      ≤ (hexColumnOfWidth a h0 T χ mem hreach hsummable hle_one).colSum x :=
  hexClosed_term_le_colSum a h0 T χ mem hreach hsummable hle_one hx [] hb hxsum

end StatMech.Universality

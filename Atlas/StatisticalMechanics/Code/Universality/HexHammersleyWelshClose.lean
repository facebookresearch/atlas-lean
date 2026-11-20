/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































































import Mathlib
import Code.Universality.HexLattice
import Code.Universality.HexBridge
import Code.Universality.HexInjections
import Code.Universality.HexConnEndgame

namespace StatMech.Universality

open scoped BigOperators














theorem hhw_critFacts_of_finsetBound {W : Type*} (f : W → ℝ)
    (hnn : ∀ w, 0 ≤ f w)
    (hbd : ∀ s : Finset W, ∑ w ∈ s, f w ≤ 1) :
    Summable f ∧ (∑' w, f w) ≤ 1 :=
  ⟨summable_of_sum_le hnn hbd, Real.tsum_le_of_sum_le hnn hbd⟩















theorem hhw_finsetBound_of_boundary {W : Type*} (f : W → ℝ)
    (cl ct : ℝ) (hcl : 0 ≤ cl) (hct : 0 ≤ ct)
    (lam tau : Finset W → ℝ)
    (hlam : ∀ s, 0 ≤ lam s) (htau : ∀ s, 0 ≤ tau s)
    (hbdry : ∀ s : Finset W, cl * lam s + ct * tau s + (∑ w ∈ s, f w) = 1) :
    ∀ s : Finset W, ∑ w ∈ s, f w ≤ 1 := by
  intro s
  have h := hbdry s
  nlinarith [mul_nonneg hcl (hlam s), mul_nonneg hct (htau s)]




theorem hhw_critSummable_of_boundary {W : Type*} (f : W → ℝ)
    (cl ct : ℝ) (hcl : 0 ≤ cl) (hct : 0 ≤ ct)
    (lam tau : Finset W → ℝ)
    (hlam : ∀ s, 0 ≤ lam s) (htau : ∀ s, 0 ≤ tau s)
    (hnn : ∀ w, 0 ≤ f w)
    (hbdry : ∀ s : Finset W, cl * lam s + ct * tau s + (∑ w ∈ s, f w) = 1) :
    Summable f :=
  summable_of_sum_le hnn
    (hhw_finsetBound_of_boundary f cl ct hcl hct lam tau hlam htau hbdry)




theorem hhw_critLeOne_of_boundary {W : Type*} (f : W → ℝ)
    (cl ct : ℝ) (hcl : 0 ≤ cl) (hct : 0 ≤ ct)
    (lam tau : Finset W → ℝ)
    (hlam : ∀ s, 0 ≤ lam s) (htau : ∀ s, 0 ≤ tau s)
    (hnn : ∀ w, 0 ≤ f w)
    (hbdry : ∀ s : Finset W, cl * lam s + ct * tau s + (∑ w ∈ s, f w) = 1) :
    (∑' w, f w) ≤ 1 :=
  Real.tsum_le_of_sum_le hnn
    (hhw_finsetBound_of_boundary f cl ct hcl hct lam tau hlam htau hbdry)















theorem hhw_finsetBound_of_singleStrip {W : Type*} (f : W → ℝ)
    (cl ct : ℝ) (hcl : 0 ≤ cl) (hct : 0 ≤ ct)
    (hnn : ∀ w, 0 ≤ f w)
    (strip : Finset W → Finset W)
    (hsub : ∀ s, s ⊆ strip s)
    (lam tau : Finset W → ℝ)
    (hlam : ∀ s, 0 ≤ lam s) (htau : ∀ s, 0 ≤ tau s)
    (hbdry : ∀ s : Finset W, cl * lam s + ct * tau s + (∑ w ∈ strip s, f w) = 1) :
    ∀ s : Finset W, ∑ w ∈ s, f w ≤ 1 := by
  intro s
  have hmono : ∑ w ∈ s, f w ≤ ∑ w ∈ strip s, f w :=
    Finset.sum_le_sum_of_subset_of_nonneg (hsub s) (fun w _ _ => hnn w)
  have h := hbdry s
  nlinarith [mul_nonneg hcl (hlam s), mul_nonneg hct (htau s), hmono]
























noncomputable def hhw_hexColumnOfBoundary (a : ℂ) (h0 : ℤ) (T : ℕ)
    (mem : List ℤ → Prop)
    (hreach : ∀ ts, mem ts →
      ∃ v ∈ (HexWalk.ofTurns a h0 ts).vertices, a.re + T ≤ v.re)
    (lam tau : Finset {ts : List ℤ // mem ts} → ℝ)
    (hlam : ∀ s, 0 ≤ lam s) (htau : ∀ s, 0 ≤ tau s)
    (hbdry : ∀ s : Finset {ts : List ℤ // mem ts},
      hexCl * lam s + hexCt * tau s
        + (∑ w ∈ s, hexChiE ^ (HexWalk.ofTurns a h0 w.1).numVertices) = 1) :
    HexColumn T hexChiE :=
  hexColumnOfWidth a h0 T hexChiE mem hreach
    (hhw_critSummable_of_boundary
      (fun w : {ts : List ℤ // mem ts} => hexChiE ^ (HexWalk.ofTurns a h0 w.1).numVertices)
      hexCl hexCt (le_of_lt hexCl_pos) (le_of_lt hexCt_pos)
      lam tau hlam htau (fun _ => pow_nonneg (le_of_lt hexChiE_pos) _) hbdry)
    (hhw_critLeOne_of_boundary
      (fun w : {ts : List ℤ // mem ts} => hexChiE ^ (HexWalk.ofTurns a h0 w.1).numVertices)
      hexCl hexCt (le_of_lt hexCl_pos) (le_of_lt hexCt_pos)
      lam tau hlam htau (fun _ => pow_nonneg (le_of_lt hexChiE_pos) _) hbdry)



theorem hhw_hexColumnOfBoundary_colSum (a : ℂ) (h0 : ℤ) (T : ℕ)
    (mem : List ℤ → Prop) (hreach lam tau hlam htau hbdry) (y : ℝ) :
    (hhw_hexColumnOfBoundary a h0 T mem hreach lam tau hlam htau hbdry).colSum y
      = ∑' w : {ts // mem ts}, y ^ (HexWalk.ofTurns a h0 w.1).numVertices := rfl




theorem hhw_hexColumnOfBoundary_critLeOne (a : ℂ) (h0 : ℤ) (T : ℕ)
    (mem : List ℤ → Prop) (hreach lam tau hlam htau hbdry) :
    ((hhw_hexColumnOfBoundary a h0 T mem hreach lam tau hlam htau hbdry).colSum hexChiE) ≤ 1 :=
  (hhw_hexColumnOfBoundary a h0 T mem hreach lam tau hlam htau hbdry).crit_le_one















theorem hhw_hexColumnOfBoundary_nonvacuous (a : ℂ) (h0 : ℤ) (T : ℕ)
    (hreach : ∀ ts, (fun _ : List ℤ => False) ts →
      ∃ v ∈ (HexWalk.ofTurns a h0 ts).vertices, a.re + T ≤ v.re) :
    ∃ lam tau : Finset {ts : List ℤ // (fun _ : List ℤ => False) ts} → ℝ,
      (∀ s, 0 ≤ lam s) ∧ (∀ s, 0 ≤ tau s) ∧
      (∀ s : Finset {ts : List ℤ // (fun _ : List ℤ => False) ts},
        hexCl * lam s + hexCt * tau s
          + (∑ w ∈ s, hexChiE ^ (HexWalk.ofTurns a h0 w.1).numVertices) = 1) := by
  refine ⟨fun _ => hexCl⁻¹, fun _ => 0,
    fun _ => le_of_lt (inv_pos.mpr hexCl_pos), fun _ => le_refl 0, ?_⟩
  intro s
  
  have hempty : s = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    rintro ⟨ts, hts⟩ _
    exact hts
  subst hempty
  simp only [Finset.sum_empty, mul_zero, add_zero]
  rw [mul_inv_cancel₀ (ne_of_gt hexCl_pos)]

end StatMech.Universality

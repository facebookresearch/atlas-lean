/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Universality.HexEndpointAggregation
import Code.Universality.HexHammersleyWelshClose

namespace StatMech.Universality

open HexWalk
open scoped BigOperators

noncomputable section



theorem hecb_endpoint_finset_bound
    {W : Type*} (f : W → ℝ)
    (hnn : ∀ w, 0 ≤ f w)
    (strip : Finset W → Finset W)
    (hsub : ∀ s, s ⊆ strip s)
    (lam tau : Finset W → ℝ)
    (hlam : ∀ s, 0 ≤ lam s) (htau : ∀ s, 0 ≤ tau s)
    (hbdry : ∀ s,
      hexCl * lam s + hexCt * tau s + ∑ w ∈ strip s, f w = 1) :
    ∀ s : Finset W, ∑ w ∈ s, f w ≤ 1 :=
  hhw_finsetBound_of_singleStrip f hexCl hexCt
    (le_of_lt hexCl_pos) (le_of_lt hexCt_pos)
    hnn strip hsub lam tau hlam htau hbdry



noncomputable def hecb_hexEndpointColumnOfSingleStrip
    (a : ℂ) (h0 : ℤ) (T : ℕ)
    (mem : List ℤ → Prop)
    (hlen : ∀ ts, mem ts → T ≤ (ofTurns a h0 ts).endpointNumVertices)
    (strip : Finset {ts : List ℤ // mem ts} →
      Finset {ts : List ℤ // mem ts})
    (hsub : ∀ s, s ⊆ strip s)
    (lam tau : Finset {ts : List ℤ // mem ts} → ℝ)
    (hlam : ∀ s, 0 ≤ lam s) (htau : ∀ s, 0 ≤ tau s)
    (hbdry : ∀ s,
      hexCl * lam s + hexCt * tau s +
        ∑ w ∈ strip s,
          hexChiE ^ (ofTurns a h0 w.1).endpointNumVertices = 1) :
    HexColumn T hexChiE where
  W := {ts : List ℤ // mem ts}
  len := fun w => (ofTurns a h0 w.1).endpointNumVertices
  len_ge := fun w => hlen w.1 w.2
  crit_summable := by
    let f : {ts : List ℤ // mem ts} → ℝ :=
      fun w => hexChiE ^ (ofTurns a h0 w.1).endpointNumVertices
    have hnn : ∀ w, 0 ≤ f w :=
      fun _ => pow_nonneg (le_of_lt hexChiE_pos) _
    have hbound : ∀ s : Finset {ts : List ℤ // mem ts},
        ∑ w ∈ s, f w ≤ 1 :=
      hecb_endpoint_finset_bound f hnn strip hsub lam tau hlam htau hbdry
    exact summable_of_sum_le (f := f) (c := 1) hnn hbound
  crit_le_one := by
    let f : {ts : List ℤ // mem ts} → ℝ :=
      fun w => hexChiE ^ (ofTurns a h0 w.1).endpointNumVertices
    have hnn : ∀ w, 0 ≤ f w :=
      fun _ => pow_nonneg (le_of_lt hexChiE_pos) _
    have hbound : ∀ s : Finset {ts : List ℤ // mem ts},
        ∑ w ∈ s, f w ≤ 1 :=
      hecb_endpoint_finset_bound f hnn strip hsub lam tau hlam htau hbdry
    exact Real.tsum_le_of_sum_le hnn hbound

theorem hecb_hexEndpointColumn_colSum
    (a : ℂ) (h0 : ℤ) (T : ℕ)
    (mem : List ℤ → Prop) (hlen strip hsub lam tau hlam htau hbdry)
    (x : ℝ) :
    (hecb_hexEndpointColumnOfSingleStrip a h0 T mem hlen strip hsub
      lam tau hlam htau hbdry).colSum x =
      ∑' w : {ts : List ℤ // mem ts},
        x ^ (ofTurns a h0 w.1).endpointNumVertices := rfl

theorem hecb_hexEndpointColumn_critical_le_one
    (a : ℂ) (h0 : ℤ) (T : ℕ)
    (mem : List ℤ → Prop) (hlen strip hsub lam tau hlam htau hbdry) :
    (hecb_hexEndpointColumnOfSingleStrip a h0 T mem hlen strip hsub
      lam tau hlam htau hbdry).colSum hexChiE ≤ 1 :=
  (hecb_hexEndpointColumnOfSingleStrip a h0 T mem hlen strip hsub
    lam tau hlam htau hbdry).crit_le_one

end

end StatMech.Universality

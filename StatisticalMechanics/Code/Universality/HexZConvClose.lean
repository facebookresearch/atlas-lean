/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Mathlib
import Code.Universality.HexInjections
import Code.Universality.HexBridgeRecon

namespace StatMech.Universality

open scoped BigOperators
open HexWalk











def hzc_truncSet (a : ℂ) (h0 : ℤ) (N : ℕ) : Set (List ℤ) :=
  {ts | (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).numVertices < N}





theorem hzc_truncSet_finite (a : ℂ) (h0 : ℤ) (N : ℕ) :
    (hzc_truncSet a h0 N).Finite := by
  apply Set.Finite.subset
    ((List.finite_length_le Bool N).image
      (fun l => l.map (fun b => if b then (1 : ℤ) else -1)))
  rintro ts ⟨hleg, hlen⟩
  have hlen' : ts.length < N := by
    have h1 : (ofTurns a h0 ts).numVertices = ts.length + 1 := by
      rw [numVertices_eq]; rfl
    omega
  refine ⟨ts.map (fun t => decide (t = 1)), ?_, ?_⟩
  · simp only [Set.mem_setOf_eq, List.length_map]; omega
  · simp only [List.map_map]
    conv_rhs => rw [← List.map_id ts]
    apply List.map_congr_left
    intro t ht
    have hmem := hleg.1 t (by simpa [ofTurns] using ht)
    rcases hmem with h | h <;> simp [h]



noncomputable def hzc_truncFinset (a : ℂ) (h0 : ℤ) (N : ℕ) : Finset (List ℤ) :=
  (hzc_truncSet_finite a h0 N).toFinset


theorem hzc_mem_truncFinset (a : ℂ) (h0 : ℤ) (N : ℕ) (ts : List ℤ) :
    ts ∈ hzc_truncFinset a h0 N ↔
      (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).numVertices < N := by
  unfold hzc_truncFinset
  rw [Set.Finite.mem_toFinset]
  rfl












noncomputable def hzc_sawCount (a : ℂ) (h0 : ℤ) (n : ℕ) : ℕ :=
  ((hzc_truncFinset a h0 (n + 1)).filter
    (fun ts => (ofTurns a h0 ts).numVertices = n)).card






theorem hzc_filterCard_eq (a : ℂ) (h0 : ℤ) (N n : ℕ) (hn : n < N) :
    ((hzc_truncFinset a h0 N).filter
        (fun ts => (ofTurns a h0 ts).numVertices = n)).card = hzc_sawCount a h0 n := by
  classical
  unfold hzc_sawCount
  congr 1
  ext ts
  simp only [Finset.mem_filter, hzc_mem_truncFinset]
  constructor
  · rintro ⟨⟨hleg, _⟩, hv⟩; exact ⟨⟨hleg, by omega⟩, hv⟩
  · rintro ⟨⟨hleg, _⟩, hv⟩; exact ⟨⟨hleg, by omega⟩, hv⟩




theorem hzc_sawCount_zero (a : ℂ) (h0 : ℤ) : hzc_sawCount a h0 0 = 0 := by
  classical
  unfold hzc_sawCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro ts _
  have : (ofTurns a h0 ts).numVertices = ts.length + 1 := by rw [numVertices_eq]; rfl
  omega











theorem hzc_trunc_wt (a : ℂ) (h0 : ℤ) (x : ℝ) (N : ℕ) {ts : List ℤ}
    (h : ts ∈ hzc_truncFinset a h0 N) :
    hexSAWwt a h0 x ts = x ^ (ofTurns a h0 ts).numVertices :=
  hexSAWwt_of_isLegalSAW a h0 x ((hzc_mem_truncFinset a h0 N ts).mp h).1











theorem hzc_partial_eq (a : ℂ) (h0 : ℤ) (x : ℝ) (N : ℕ) :
    ∑ ts ∈ hzc_truncFinset a h0 N, hexSAWwt a h0 x ts
      = ∑ n ∈ Finset.range N, (hzc_sawCount a h0 n : ℝ) * x ^ n := by
  classical
  rw [Finset.sum_congr rfl (fun ts h => hzc_trunc_wt a h0 x N h)]
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.range N)
        (g := fun ts => (ofTurns a h0 ts).numVertices) ?_]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_range] at hn
    rw [Finset.sum_congr rfl (g := fun _ => x ^ n)
          (fun ts hts => by simp only [Finset.mem_filter] at hts; rw [hts.2])]
    rw [Finset.sum_const, nsmul_eq_mul, hzc_filterCard_eq a h0 N n hn]
  · intro ts hts
    simp only [Finset.mem_range]
    exact ((hzc_mem_truncFinset a h0 N ts).mp hts).2











def hzc_Dn (a : ℂ) (h0 : ℤ) (N : ℕ) : Type := {ts : List ℤ // ts ∈ hzc_truncFinset a h0 N}

noncomputable instance hzc_Dn_fintype (a : ℂ) (h0 : ℤ) (N : ℕ) :
    Fintype (hzc_Dn a h0 N) := by
  unfold hzc_Dn; infer_instance



noncomputable def hzc_wtγ (a : ℂ) (h0 : ℤ) (x : ℝ) (N : ℕ) (d : hzc_Dn a h0 N) : ℝ :=
  hexSAWwt a h0 x d.1


theorem hzc_wtγ_nn (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) (N : ℕ)
    (d : hzc_Dn a h0 N) : 0 ≤ hzc_wtγ a h0 x N d :=
  hexSAWwt_nonneg a h0 hx d.1






theorem hzc_partial_eq_attach (a : ℂ) (h0 : ℤ) (x : ℝ) (N : ℕ) :
    ∑ d : hzc_Dn a h0 N, hzc_wtγ a h0 x N d
      = ∑ n ∈ Finset.range N, (hzc_sawCount a h0 n : ℝ) * x ^ n := by
  rw [show (∑ d : hzc_Dn a h0 N, hzc_wtγ a h0 x N d)
        = ∑ ts ∈ hzc_truncFinset a h0 N, hexSAWwt a h0 x ts from
      Finset.sum_coe_sort (hzc_truncFinset a h0 N) (hexSAWwt a h0 x)]
  exact hzc_partial_eq a h0 x N









theorem hzc_nil_isLegalSAW (a : ℂ) (h0 : ℤ) : (ofTurns a h0 []).IsLegalSAW := by
  refine ⟨?_, ?_⟩
  · intro t ht; simp only [ofTurns_turns, List.not_mem_nil] at ht
  · unfold IsSAW vertices
    simp only [ofTurns_startMid, ofTurns_h0, ofTurns_turns, verticesAux_nil]
    exact List.nodup_singleton _




theorem hzc_nil_mem_truncFinset (a : ℂ) (h0 : ℤ) {N : ℕ} (hN : 2 ≤ N) :
    [] ∈ hzc_truncFinset a h0 N := by
  rw [hzc_mem_truncFinset]
  refine ⟨hzc_nil_isLegalSAW a h0, ?_⟩
  have : (ofTurns a h0 []).numVertices = 1 := by
    rw [numVertices_eq]; rfl
  omega




theorem hzc_sawCount_one_pos (a : ℂ) (h0 : ℤ) : 1 ≤ hzc_sawCount a h0 1 := by
  classical
  unfold hzc_sawCount
  rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  push Not
  refine ⟨[], hzc_nil_mem_truncFinset a h0 (le_refl 2), ?_⟩
  rw [numVertices_eq]; rfl

end StatMech.Universality

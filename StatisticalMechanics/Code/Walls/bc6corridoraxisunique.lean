/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































import Mathlib
import Code.Walls.bc3_core

open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths

namespace StatMech

namespace Walls

variable {d : ℕ}










lemma bc6_corridorEdge_endpoints {j : Fin d} {L : ℕ} {u v : Site d}
    (hmem : s(u, v) ∈ hrHD_corridorEdges j L) (hno0 : (0 : Site d) ∉ s(u, v)) :
    ∃ p : ℕ, 1 ≤ p ∧ p < L ∧
      ((u = hrHD_rayPt j (p : ℤ) ∧ v = hrHD_rayPt j ((p : ℤ) + 1)) ∨
       (u = hrHD_rayPt j ((p : ℤ) + 1) ∧ v = hrHD_rayPt j (p : ℤ))) := by
  obtain ⟨p, hp, hpe⟩ := bc3_corridorEdge_structure hmem
  
  have hp1 : 1 ≤ p := by
    by_contra hlt
    have hp0 : p = 0 := by omega
    subst hp0
    apply hno0; rw [hpe]; simp only [Nat.cast_zero, hrHD_rayPt_zero]; exact Sym2.mem_mk_left _ _
  refine ⟨p, hp1, hp, ?_⟩
  
  rw [Sym2.eq_iff] at hpe
  tauto




lemma bc6_endpoint_is_rayPt {k : Fin d} {L : ℕ} {u v : Site d}
    (hmem : s(u, v) ∈ hrHD_corridorEdges k L) (hno0 : (0 : Site d) ∉ s(u, v))
    {w : Site d} (hw : w ∈ s(u, v)) :
    ∃ p : ℕ, 1 ≤ p ∧ p ≤ L ∧ w = hrHD_rayPt k (p : ℤ) := by
  obtain ⟨p, hp, hpe⟩ := bc3_corridorEdge_structure hmem
  have hp1 : 1 ≤ p := by
    by_contra hlt
    have hp0 : p = 0 := by omega
    subst hp0
    apply hno0; rw [hpe]; simp only [Nat.cast_zero, hrHD_rayPt_zero]; exact Sym2.mem_mk_left _ _
  rw [hpe, Sym2.mem_iff] at hw
  rcases hw with rfl | rfl
  · exact ⟨p, hp1, le_of_lt hp, rfl⟩
  · refine ⟨p + 1, by omega, by omega, ?_⟩
    have : ((p : ℤ) + 1) = ((p + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this]




lemma bc6_endpoint_axis_value_ne_zero {k : Fin d} {L : ℕ} {u v : Site d}
    (hmem : s(u, v) ∈ hrHD_corridorEdges k L) (hno0 : (0 : Site d) ∉ s(u, v))
    {w : Site d} (hw : w ∈ s(u, v)) :
    w k ≠ 0 ∧ ∀ i : Fin d, i ≠ k → w i = 0 := by
  obtain ⟨p, hp1, _hpL, hwe⟩ := bc6_endpoint_is_rayPt hmem hno0 hw
  subst hwe
  refine ⟨?_, ?_⟩
  · rw [hrHD_rayPt_self]; exact_mod_cast (by omega : (p : ℤ) ≠ 0)
  · intro i hi; exact hrHD_rayPt_of_ne k (p : ℤ) hi













lemma bc6_rayPt_notMem_crossCorridor {k m : Fin d} (hkm : k ≠ m) {L : ℕ} {q : ℤ} (hq : q ≠ 0)
    {u v : Site d} (hmem : s(u, v) ∈ hrHD_corridorEdges k L) :
    (hrHD_rayPt m q : Site d) ∉ s(u, v) := by
  intro hin
  obtain ⟨p, _hp, hpe⟩ := bc3_corridorEdge_structure hmem
  rw [hpe, Sym2.mem_iff] at hin
  rcases hin with heq | heq
  · 
    exact hrHD_rayPt_disjoint_of_ne (Ne.symm hkm) hq heq
  · 
    exact hrHD_rayPt_disjoint_of_ne (Ne.symm hkm) hq heq





lemma bc6_endpoint_not_crossRayPt {k m : Fin d} (hkm : k ≠ m) {L : ℕ}
    {u v : Site d} (hmem : s(u, v) ∈ hrHD_corridorEdges k L) (hno0 : (0 : Site d) ∉ s(u, v))
    {w : Site d} (hw : w ∈ s(u, v)) (q : ℤ) :
    w ≠ hrHD_rayPt m q := by
  obtain ⟨p, hp1, _hpL, hwe⟩ := bc6_endpoint_is_rayPt hmem hno0 hw
  subst hwe
  
  exact hrHD_rayPt_disjoint_of_ne hkm (by exact_mod_cast (by omega : (p : ℤ) ≠ 0))









lemma bc6_corridorEdges_endpoints_disjoint {k m : Fin d} (hkm : k ≠ m) {L₁ L₂ : ℕ}
    {u v u' v' : Site d}
    (hmem₁ : s(u, v) ∈ hrHD_corridorEdges k L₁)
    (hmem₂ : s(u', v') ∈ hrHD_corridorEdges m L₂) (hno0₂ : (0 : Site d) ∉ s(u', v'))
    {w : Site d} (hw₁ : w ∈ s(u, v)) (hw₂ : w ∈ s(u', v')) : False := by
  
  obtain ⟨q, hq1, _hqL, hwq⟩ := bc6_endpoint_is_rayPt hmem₂ hno0₂ hw₂
  
  have hqne : (q : ℤ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  refine bc6_rayPt_notMem_crossCorridor hkm (q := (q : ℤ)) hqne hmem₁ ?_
  rwa [← hwq]

end Walls

end StatMech

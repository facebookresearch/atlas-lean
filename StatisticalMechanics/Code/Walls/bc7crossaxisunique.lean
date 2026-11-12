/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































import Mathlib
import Code.Walls.bc3_core
import Code.Walls.bc6corridoraxisunique
import Code.Walls.bc6raysetdef

open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths

namespace StatMech

namespace Walls

variable {d : ℕ}












theorem bc7_crossAxisUnique {k m : Fin d} (hkm : k ≠ m) {L : ℕ} {q : ℤ} (hq : q ≠ 0)
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





theorem bc7_crossAxisUnique_of_corridorAxisUnique {k m : Fin d} (hkm : k ≠ m) {L : ℕ}
    {q : ℤ} (hq : q ≠ 0) {u v : Site d} (hmem : s(u, v) ∈ hrHD_corridorEdges k L) :
    (hrHD_rayPt m q : Site d) ∉ s(u, v) :=
  bc6_rayPt_notMem_crossCorridor hkm hq hmem



theorem bc7_crossAxisUnique_nat {k m : Fin d} (hkm : k ≠ m) {L p : ℕ} (hp : 1 ≤ p)
    {u v : Site d} (hmem : s(u, v) ∈ hrHD_corridorEdges k L) :
    (hrHD_rayPt m (p : ℤ) : Site d) ∉ s(u, v) :=
  bc7_crossAxisUnique hkm (by exact_mod_cast (by omega : (p : ℤ) ≠ 0)) hmem






theorem bc7_endpoint_ne_crossRayPt {k m : Fin d} (hkm : k ≠ m) {L : ℕ} {q : ℤ} (hq : q ≠ 0)
    {u v : Site d} (hmem : s(u, v) ∈ hrHD_corridorEdges k L)
    {w : Site d} (hw : w ∈ s(u, v)) :
    w ≠ hrHD_rayPt m q := by
  intro hwq
  exact bc7_crossAxisUnique hkm hq hmem (hwq ▸ hw)




theorem bc7_crossCorridor_endpoints_disjoint {k m : Fin d} (hkm : k ≠ m) {L₁ L₂ : ℕ}
    {u v u' v' : Site d}
    (hmem₁ : s(u, v) ∈ hrHD_corridorEdges k L₁)
    (hmem₂ : s(u', v') ∈ hrHD_corridorEdges m L₂) (hno0₂ : (0 : Site d) ∉ s(u', v'))
    {w : Site d} (hw₁ : w ∈ s(u, v)) (hw₂ : w ∈ s(u', v')) : False :=
  bc6_corridorEdges_endpoints_disjoint hkm hmem₁ hmem₂ hno0₂ hw₁ hw₂












theorem bc7_crossRayPt_notMem_rayInterior {k m : Fin d} (hkm : k ≠ m) {L : ℕ} (q : ℤ) :
    (hrHD_rayPt m q : Site d) ∉ bc6_rayInterior k L := by
  rw [bc6_mem_rayInterior]
  rintro ⟨p, ⟨hp1, _hpL⟩, heq⟩
  
  exact hrHD_rayPt_disjoint_of_ne hkm
    (by exact_mod_cast (by omega : (p : ℤ) ≠ 0)) heq.symm




theorem bc7_rayInteriors_disjoint {k m : Fin d} (hkm : k ≠ m) {L₁ L₂ : ℕ} :
    Disjoint (bc6_rayInterior k L₁) (bc6_rayInterior m L₂) := by
  rw [Set.disjoint_left]
  intro x hxk hxm
  rw [bc6_mem_rayInterior] at hxk
  obtain ⟨p, ⟨hp1, _hpL⟩, hxp⟩ := hxk
  
  exact bc7_crossRayPt_notMem_rayInterior (Ne.symm hkm) (q := (p : ℤ)) (hxp ▸ hxm)

end Walls

end StatMech

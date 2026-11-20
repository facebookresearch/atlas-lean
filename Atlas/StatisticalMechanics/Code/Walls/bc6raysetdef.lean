/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































import Mathlib
import Code.Walls.bc3_core
import Code.Percolation.Exploration

open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths

namespace StatMech

namespace Walls

variable {d : ℕ}






def bc6_rayInterior (a : Fin d) (R : ℕ) : Set (Site d) :=
  {x | ∃ p : ℕ, (1 ≤ p ∧ p ≤ R) ∧ x = hrHD_rayPt a (p : ℤ)}



lemma bc6_mem_rayInterior {a : Fin d} {R : ℕ} {x : Site d} :
    x ∈ bc6_rayInterior a R ↔ ∃ p : ℕ, (1 ≤ p ∧ p ≤ R) ∧ x = hrHD_rayPt a (p : ℤ) :=
  Iff.rfl


lemma bc6_rayPt_mem_rayInterior {a : Fin d} {R p : ℕ} (h1 : 1 ≤ p) (h2 : p ≤ R) :
    hrHD_rayPt a (p : ℤ) ∈ bc6_rayInterior a R :=
  ⟨p, ⟨h1, h2⟩, rfl⟩


lemma bc6_mouth_mem_rayInterior {a : Fin d} {R : ℕ} (hR : 1 ≤ R) :
    (hrHD_rayPt a 1 : Site d) ∈ bc6_rayInterior a R := by
  have h : hrHD_rayPt a ((1 : ℕ) : ℤ) = hrHD_rayPt a 1 := by norm_num
  rw [← h]
  exact bc6_rayPt_mem_rayInterior le_rfl hR



lemma bc6_origin_notMem_rayInterior {a : Fin d} {R : ℕ} :
    (0 : Site d) ∉ bc6_rayInterior a R := by
  rintro ⟨p, ⟨hp1, _⟩, hp0⟩
  have : hrHD_rayPt a (p : ℤ) = (0 : Site d) := hp0.symm
  rw [hrHD_rayPt_eq_zero_iff] at this
  omega













def bc6_offBoxCluster (N : ℕ) (a : Fin d) (R : ℕ) (ω : ConfigSpace (Sym2 (Site d))) :
    Set (Site d) :=
  clusterWithin d (removeSite 0 ω) (box d N)ᶜ (hrHD_rayPt a (R : ℤ))


lemma bc6_offBoxCluster_subset_offBox {N : ℕ} {a : Fin d} {R : ℕ}
    {ω : ConfigSpace (Sym2 (Site d))} :
    bc6_offBoxCluster N a R ω ⊆ (box d N)ᶜ := by
  rintro x ⟨hxS, _, _⟩
  exact hxS


lemma bc6_mem_offBoxCluster_offBox {N : ℕ} {a : Fin d} {R : ℕ}
    {ω : ConfigSpace (Sym2 (Site d))} {x : Site d}
    (hx : x ∈ bc6_offBoxCluster N a R ω) : x ∉ box d N :=
  bc6_offBoxCluster_subset_offBox hx



lemma bc6_farEnd_notMem_box {N : ℕ} {a : Fin d} {R : ℕ} (hNR : N < R) :
    (hrHD_rayPt a (R : ℤ)) ∉ box d N := by
  rw [mem_box, not_forall]
  refine ⟨a, ?_⟩
  rw [hrHD_rayPt_self]
  simp only [Int.natAbs_natCast]
  omega



lemma bc6_farEnd_mem_offBoxCluster {N : ℕ} {a : Fin d} {R : ℕ} (hNR : N < R)
    (ω : ConfigSpace (Sym2 (Site d))) :
    (hrHD_rayPt a (R : ℤ)) ∈ bc6_offBoxCluster N a R ω := by
  have hoff : (hrHD_rayPt a (R : ℤ)) ∈ (box d N)ᶜ := bc6_farEnd_notMem_box hNR
  exact ⟨hoff, hoff, connectedWithin_refl _ _ _⟩














def bc6_armRegion (N : ℕ) (a : Fin d) (R : ℕ) (ω : ConfigSpace (Sym2 (Site d))) :
    Set (Site d) :=
  bc6_rayInterior a R ∪ bc6_offBoxCluster N a R ω



lemma bc6_mem_armRegion {N : ℕ} {a : Fin d} {R : ℕ} {ω : ConfigSpace (Sym2 (Site d))}
    {x : Site d} :
    x ∈ bc6_armRegion N a R ω ↔
      x ∈ bc6_rayInterior a R ∨ x ∈ bc6_offBoxCluster N a R ω :=
  Set.mem_union _ _ _


lemma bc6_rayInterior_subset_armRegion {N : ℕ} {a : Fin d} {R : ℕ}
    {ω : ConfigSpace (Sym2 (Site d))} :
    bc6_rayInterior a R ⊆ bc6_armRegion N a R ω :=
  Set.subset_union_left


lemma bc6_offBoxCluster_subset_armRegion {N : ℕ} {a : Fin d} {R : ℕ}
    {ω : ConfigSpace (Sym2 (Site d))} :
    bc6_offBoxCluster N a R ω ⊆ bc6_armRegion N a R ω :=
  Set.subset_union_right


lemma bc6_rayPt_mem_armRegion {N : ℕ} {a : Fin d} {R p : ℕ} {ω : ConfigSpace (Sym2 (Site d))}
    (h1 : 1 ≤ p) (h2 : p ≤ R) :
    hrHD_rayPt a (p : ℤ) ∈ bc6_armRegion N a R ω :=
  bc6_rayInterior_subset_armRegion (bc6_rayPt_mem_rayInterior h1 h2)


lemma bc6_mouth_mem_armRegion {N : ℕ} {a : Fin d} {R : ℕ} {ω : ConfigSpace (Sym2 (Site d))}
    (hR : 1 ≤ R) :
    (hrHD_rayPt a 1 : Site d) ∈ bc6_armRegion N a R ω :=
  bc6_rayInterior_subset_armRegion (bc6_mouth_mem_rayInterior hR)



lemma bc6_farEnd_mem_armRegion {N : ℕ} {a : Fin d} {R : ℕ} (hNR : N < R)
    (ω : ConfigSpace (Sym2 (Site d))) :
    (hrHD_rayPt a (R : ℤ)) ∈ bc6_armRegion N a R ω :=
  bc6_offBoxCluster_subset_armRegion (bc6_farEnd_mem_offBoxCluster hNR ω)

end Walls

end StatMech

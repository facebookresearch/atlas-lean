/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































import Mathlib
import Code.Percolation.HrouteHighDim

open Set
open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}










theorem bc_wiring_forces_open_eq_true (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L t : ℕ)
    (ht : t < L) :
    forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω
        s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) = true := by
  
  have hmem : s(hrHD_rayPt j (((t + 1 : ℕ) : ℤ)), hrHD_rayPt j (((t + 1 : ℕ) : ℤ) + 1))
      ∈ hrHD_corridorEdges j (L + 1) := hrHD_mem_corridorEdges (by omega)
  
  have he : s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2))
      = s(hrHD_rayPt j (((t + 1 : ℕ) : ℤ)), hrHD_rayPt j (((t + 1 : ℕ) : ℤ) + 1)) := by
    push_cast; ring_nf
  rw [he]
  
  exact forceOpenFinset_of_mem hmem ω








theorem bc_wiring_forces_open (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L t : ℕ)
    (ht : t < L) :
    IsOpenEdge d (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)
      (hrHD_rayPt j ((t : ℤ) + 1)) (hrHD_rayPt j ((t : ℤ) + 2)) := by
  refine ⟨?_, ?_⟩
  · 
    have hadj := hrHD_adj_rayPt j ((t : ℤ) + 1)
    have he : ((t : ℤ) + 1 + 1) = ((t : ℤ) + 2) := by ring
    rwa [he] at hadj
  · 
    exact bc_wiring_forces_open_eq_true ω j L t ht








theorem bc_wiring_forces_open_all (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ) :
    ∀ t : ℕ, t < L →
      IsOpenEdge d (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)
        (hrHD_rayPt j ((t : ℤ) + 1)) (hrHD_rayPt j ((t : ℤ) + 2)) :=
  fun t ht => bc_wiring_forces_open ω j L t ht

end Walls

end StatMech

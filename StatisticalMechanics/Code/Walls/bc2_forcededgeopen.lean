/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Mathlib
import Code.Walls.bkm_dccstepopen
import Code.Walls.bc_wiringforcesopen
import Code.Percolation.HrouteHighDim

open Set
open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}













theorem bc2_forced_edge_open_eq_true (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) {u v : Site d}
    (hmem : s(u, v) ∈ W) (h0 : (0 : Site d) ∉ s(u, v)) :
    removeSite 0 (forceOpenFinset W ω) s(u, v) = true :=
  bkm_dcc_step_open_eq_true ω W hmem h0









theorem bc2_forced_edge_open (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) {u v : Site d}
    (hadj : (hypercubicLattice d).Adj u v)
    (hmem : s(u, v) ∈ W) (h0 : (0 : Site d) ∉ s(u, v)) :
    IsOpenEdge d (removeSite 0 (forceOpenFinset W ω)) u v :=
  bkm_dcc_step_open ω W hadj hmem h0












theorem bc2_forced_edge_open_mem (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) {e : Sym2 (Site d)}
    (hmem : e ∈ W) (h0 : (0 : Site d) ∉ e) :
    removeSite 0 (forceOpenFinset W ω) e = true := by
  induction e using Sym2.ind with
  | _ u v => exact bc2_forced_edge_open_eq_true ω W hmem h0





def bc2_IsLatticeWiring (W : Finset (Sym2 (Site d))) : Prop :=
  ∀ u v : Site d, s(u, v) ∈ W → (hypercubicLattice d).Adj u v








theorem bc2_forced_edge_open_all (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) (hW : bc2_IsLatticeWiring W) :
    ∀ u v : Site d, s(u, v) ∈ W → (0 : Site d) ∉ s(u, v) →
      IsOpenEdge d (removeSite 0 (forceOpenFinset W ω)) u v :=
  fun u v hmem h0 => bc2_forced_edge_open ω W (hW u v hmem) hmem h0













theorem bc2_corridor_isLatticeWiring (j : Fin d) (L : ℕ) :
    bc2_IsLatticeWiring (hrHD_corridorEdges j L) := by
  intro u v hmem
  rw [hrHD_corridorEdges, Finset.mem_image] at hmem
  obtain ⟨t, _, het⟩ := hmem
  rw [Sym2.eq_iff] at het
  rcases het with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1; subst h2; exact hrHD_adj_rayPt j (t : ℤ)
  · subst h1; subst h2; exact (hrHD_adj_rayPt j (t : ℤ)).symm









theorem bc2_forced_edge_open_corridor (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ) :
    ∀ u v : Site d, s(u, v) ∈ hrHD_corridorEdges j L → (0 : Site d) ∉ s(u, v) →
      IsOpenEdge d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j L) ω)) u v :=
  bc2_forced_edge_open_all ω (hrHD_corridorEdges j L) (bc2_corridor_isLatticeWiring j L)











theorem bc2_forced_edge_open_interior_step (ω : ConfigSpace (Sym2 (Site d)))
    (j : Fin d) (L t : ℕ) (ht : t < L) :
    IsOpenEdge d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))
      (hrHD_rayPt j ((t : ℤ) + 1)) (hrHD_rayPt j ((t : ℤ) + 2)) := by
  
  have hmem : s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2))
      ∈ hrHD_corridorEdges j (L + 1) := by
    have h := hrHD_mem_corridorEdges (j := j) (L := L + 1) (t := t + 1) (by omega)
    have he : s(hrHD_rayPt j (((t + 1 : ℕ) : ℤ)), hrHD_rayPt j (((t + 1 : ℕ) : ℤ) + 1))
        = s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) := by
      push_cast; ring_nf
    rwa [he] at h
  
  have h0 : (0 : Site d) ∉ s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) := by
    have h := hrHD_origin_notMem_rayEdge j ((t : ℤ) + 1) (by omega)
    have he : s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 1 + 1))
        = s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) := by ring_nf
    rwa [he] at h
  exact bc2_forced_edge_open_corridor ω j (L + 1) _ _ hmem h0

end Walls

end StatMech

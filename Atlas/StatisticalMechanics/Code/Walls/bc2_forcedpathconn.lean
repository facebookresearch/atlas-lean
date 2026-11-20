/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































import Mathlib
import Code.Percolation.HrouteHighDim
import Code.Percolation.HrouteDisjointPaths
import Code.Walls.bc_wiringforcesopen
import Code.Walls.bc_mouthcorridor

open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths

namespace StatMech

namespace Walls

variable {d : ℕ}



















theorem bc2_forcedPath_connected_of_chain (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) {p q : Site d}
    (h : Relation.ReflTransGen (CorridorStep W) p q) :
    Connected d (removeSite 0 (forceOpenFinset W ω)) p q := by
  induction h with
  | refl => exact connected_rfl
  | tail _ hstep ih =>
    obtain ⟨hadj, hmem, h0⟩ := hstep
    exact ih.trans
      (IsOpenEdge.connected (isOpenEdge_removeSite_forceOpen_step ω W hadj hmem h0))














theorem bc2_corridorStep (j : Fin d) (L : ℕ) (s : ℕ) (h1 : 1 ≤ s) (hsL : s ≤ L) :
    CorridorStep (hrHD_corridorEdges j (L + 1))
      (hrHD_rayPt j (s : ℤ)) (hrHD_rayPt j ((s : ℤ) + 1)) :=
  ⟨hrHD_adj_rayPt j (s : ℤ),
   hrHD_mem_corridorEdges (by omega : s < L + 1),
   hrHD_origin_notMem_rayEdge j (s : ℤ) (by exact_mod_cast h1)⟩











theorem bc2_corridorChain (j : Fin d) (L : ℕ) (m : ℕ) (hm1 : 1 ≤ m) (hmL : m ≤ L + 1) :
    Relation.ReflTransGen (CorridorStep (hrHD_corridorEdges j (L + 1)))
      (hrHD_rayPt j 1) (hrHD_rayPt j (m : ℤ)) := by
  induction m with
  | zero => exact absurd hm1 (by omega)
  | succ p ih =>
    rcases Nat.lt_or_ge 1 (p + 1) with hp | hp
    · 
      have hp1 : 1 ≤ p := by omega
      have hppL : p ≤ L := by omega
      have hrec := ih hp1 (by omega)
      have hstep : CorridorStep (hrHD_corridorEdges j (L + 1))
          (hrHD_rayPt j (p : ℤ)) (hrHD_rayPt j ((p : ℤ) + 1)) :=
        bc2_corridorStep j L p hp1 hppL
      have hchain := hrec.tail hstep
      have he : ((p : ℤ) + 1) = ((p + 1 : ℕ) : ℤ) := by push_cast; ring
      rwa [he] at hchain
    · 
      have hp1 : p + 1 = 1 := by omega
      rw [hp1]
      have : ((1 : ℕ) : ℤ) = (1 : ℤ) := by norm_num
      rw [this]













theorem bc2_forcedPathConn (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (m : ℕ) (hm1 : 1 ≤ m) (hmL : m ≤ L + 1) :
    Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))
      (hrHD_rayPt j 1) (hrHD_rayPt j (m : ℤ)) :=
  bc2_forcedPath_connected_of_chain ω (hrHD_corridorEdges j (L + 1))
    (bc2_corridorChain j L m hm1 hmL)




theorem bc2_forcedPathConn_farEnd (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ) :
    Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))
      (hrHD_rayPt j 1) (hrHD_rayPt j ((L : ℤ) + 1)) := by
  have h := bc2_forcedPathConn ω j L (L + 1) (by omega) le_rfl
  have he : (((L + 1 : ℕ) : ℤ)) = ((L : ℤ) + 1) := by push_cast; ring
  rwa [he] at h













theorem bc2_corridorMouth_forced_open (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (L t : ℕ) (ht : t < L) :
    IsOpenEdge d (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)
      (hrHD_rayPt j ((t : ℤ) + 1)) (hrHD_rayPt j ((t : ℤ) + 2)) :=
  bc_wiring_forces_open ω j L t ht











theorem bc2_corridorChain_one_step (j : Fin d) (L : ℕ) (hL : 1 ≤ L) :
    CorridorStep (hrHD_corridorEdges j (L + 1))
      (hrHD_rayPt j 1) (hrHD_rayPt j 2) := by
  have h := bc2_corridorStep j L 1 le_rfl hL
  have he2 : ((1 : ℕ) : ℤ) + 1 = (2 : ℤ) := by norm_num
  have he1 : ((1 : ℕ) : ℤ) = (1 : ℤ) := by norm_num
  rw [he2] at h
  rw [he1] at h
  exact h




theorem bc2_farEnd_ne_mouth (j : Fin d) (L : ℕ) (hL : 1 ≤ L) :
    (hrHD_rayPt j ((L : ℤ) + 1) : Site d) ≠ hrHD_rayPt j 1 :=
  bc_farEnd_ne_neighbour j L hL

end Walls

end StatMech

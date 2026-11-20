/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































import Mathlib
import Code.Percolation.HrouteHighDim
import Code.Walls.bkm_dccstepopen

open Set
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Walls

variable {d : ℕ}

open StatMech.Percolation












noncomputable def bc_mouthCutConfig (j : Fin d) (L : ℕ)
    (ω : ConfigSpace (Sym2 (Site d))) : ConfigSpace (Sym2 (Site d)) :=
  removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)



















theorem bc_mouthCorridor_step_open (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (s : ℕ) (h1 : 1 ≤ s) (hsL : s ≤ L) :
    IsOpenEdge d (bc_mouthCutConfig j L ω)
      (hrHD_rayPt j (s : ℤ)) (hrHD_rayPt j ((s : ℤ) + 1)) :=
  bkm_dcc_step_open ω (hrHD_corridorEdges j (L + 1))
    (hrHD_adj_rayPt j (s : ℤ))
    (hrHD_mem_corridorEdges (by omega : s < L + 1))
    (hrHD_origin_notMem_rayEdge j (s : ℤ) (by exact_mod_cast h1))























theorem bc_mouthCorridor_connected_to (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (L : ℕ) (m : ℕ) (hm1 : 1 ≤ m) (hmL : m ≤ L + 1) :
    Connected d (bc_mouthCutConfig j L ω)
      (hrHD_rayPt j 1) (hrHD_rayPt j (m : ℤ)) := by
  induction m with
  | zero => exact absurd hm1 (by omega)
  | succ p ih =>
    rcases Nat.lt_or_ge 1 (p + 1) with hp | hp
    · 
      
      have hp1 : 1 ≤ p := by omega
      have hppL : p ≤ L := by omega
      have hstep : IsOpenEdge d (bc_mouthCutConfig j L ω)
          (hrHD_rayPt j (p : ℤ)) (hrHD_rayPt j ((p : ℤ) + 1)) :=
        bc_mouthCorridor_step_open ω j L p hp1 hppL
      have hrec : Connected d (bc_mouthCutConfig j L ω)
          (hrHD_rayPt j 1) (hrHD_rayPt j (p : ℤ)) := ih hp1 (by omega)
      have hgoal := hrec.trans hstep.connected
      have he : ((p : ℤ) + 1) = ((p + 1 : ℕ) : ℤ) := by push_cast; ring
      rwa [he] at hgoal
    · 
      have hp1 : p + 1 = 1 := by omega
      rw [hp1]; simpa using connected_rfl




theorem bc_mouthCorridor_reaches_farEnd (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (L : ℕ) :
    Connected d (bc_mouthCutConfig j L ω)
      (hrHD_rayPt j 1) (hrHD_rayPt j ((L : ℤ) + 1)) := by
  have h := bc_mouthCorridor_connected_to ω j L (L + 1) (by omega) le_rfl
  have he : (((L + 1 : ℕ) : ℤ)) = ((L : ℤ) + 1) := by push_cast; ring
  rwa [he] at h










theorem bc_corridorCell_ne_origin (j : Fin d) (m : ℕ) (hm : 1 ≤ m) :
    (hrHD_rayPt j (m : ℤ) : Site d) ≠ 0 := by
  rw [Ne, hrHD_rayPt_eq_zero_iff]
  intro h
  have : m = 0 := by exact_mod_cast h
  omega




theorem bc_farEnd_ne_neighbour (j : Fin d) (L : ℕ) (hL : 1 ≤ L) :
    (hrHD_rayPt j ((L : ℤ) + 1) : Site d) ≠ hrHD_rayPt j 1 := by
  intro h
  have hh := congrFun h j
  rw [hrHD_rayPt_self, hrHD_rayPt_self] at hh
  
  have : (L : ℤ) + 1 = 1 := hh
  omega

end Walls

end StatMech

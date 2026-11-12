/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































import Mathlib
import Code.Percolation.HrouteHighDim

open StatMech.Lattice StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}





theorem bkm_dccrayPt_adj_origin (j : Fin d) :
    (hypercubicLattice d).Adj (0 : Site d) (hrHD_rayPt j 1) :=
  hrHD_adj_origin_rayPt_one j






theorem bkm_dccrayPt_eq_iff_of_ne {i j : Fin d} (h : i ≠ j) (s t : ℤ) :
    (hrHD_rayPt i s : Site d) = hrHD_rayPt j t ↔ (s = 0 ∧ t = 0) := by
  constructor
  · intro he
    
    have hi := congrFun he i
    rw [hrHD_rayPt_self, hrHD_rayPt_of_ne j t h] at hi
    
    have hj := congrFun he j
    rw [hrHD_rayPt_self, hrHD_rayPt_of_ne i s (Ne.symm h)] at hj
    exact ⟨hi, hj.symm⟩
  · rintro ⟨rfl, rfl⟩
    
    simp




theorem bkm_dccrayPt_ne_of_ne {i j : Fin d} (h : i ≠ j) {s t : ℤ} (hs : s ≠ 0) :
    (hrHD_rayPt i s : Site d) ≠ hrHD_rayPt j t := by
  intro he
  exact hs ((bkm_dccrayPt_eq_iff_of_ne h s t).1 he).1









theorem bkm_dccrayPt :
    (∀ j : Fin d, (hypercubicLattice d).Adj (0 : Site d) (hrHD_rayPt j 1)) ∧
      (∀ {i j : Fin d}, i ≠ j → ∀ s t : ℤ,
        ((hrHD_rayPt i s : Site d) = hrHD_rayPt j t ↔ (s = 0 ∧ t = 0))) :=
  ⟨bkm_dccrayPt_adj_origin, fun h s t => bkm_dccrayPt_eq_iff_of_ne h s t⟩

end Walls

end StatMech

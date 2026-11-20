/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.ContourLinksExits
import Code.Lattice.NoPinchDual

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice












theorem kc_vertStep_dir {K : Set (Site 2)} (e : Dart)
    (hv : (dartFace e) 0 = (dartFace (dartNext K e)) 0) :
    e.dir = ![1, 0] ∨ e.dir = ![-1, 0] := by
  rcases dartDir_cases e with hd | hd | hd | hd
  · exact Or.inl hd
  · exact Or.inr hd
  · exfalso
    rw [dartFace_of_dir_up e hd, dartFace_next_of_dir_up K e hd] at hv
    simp only [Matrix.cons_val_zero] at hv; omega
  · exfalso
    rw [dartFace_of_dir_down e hd, dartFace_next_of_dir_down K e hd] at hv
    simp only [Matrix.cons_val_zero] at hv; omega














theorem kc_vertStep_left_of_minCol {K : Set (Site 2)} (m : ℤ) (hm : ∀ w ∈ K, m ≤ w 0)
    {e : Dart} (he : IsBoundaryDart K e)
    (hvert : (dartFace e) 0 = (dartFace (dartNext K e)) 0)
    (hcol : (dartFace e) 0 ≤ m - 1) :
    e.dir = ![-1, 0] := by
  rcases kc_vertStep_dir e hvert with hd | hd
  · 
    exfalso
    have hP00 : npd_P00 (dartFace e) ∈ K := (npd_corners_right he hd).1
    rw [npd_P00] at hP00
    have hge : m ≤ (![(dartFace e) 0, (dartFace e) 1] : Site 2) 0 := hm _ hP00
    simp only [Matrix.cons_val_zero] at hge
    omega
  · exact hd

end Walls

end StatMech

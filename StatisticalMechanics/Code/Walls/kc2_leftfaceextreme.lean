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
import Code.Lattice.Umlaufsatz
import Code.Lattice.NoPinchDual

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice













theorem kc2_vertStep_dir {K : Set (Site 2)} (e : Dart)
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














theorem kc2_extremeCell_eq_tail_of_left (e : Dart) (hd : e.dir = ![-1, 0]) :
    (![dartFace e 0 + 1, dartFace e 1 + 1] : Site 2) = e.tail :=
  (dartFace_tail_of_dir_left e hd).symm







theorem kc2_extremeCell_mem_of_left {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e)
    (hd : e.dir = ![-1, 0]) :
    (![dartFace e 0 + 1, dartFace e 1 + 1] : Site 2) ∈ K := by
  rw [kc2_extremeCell_eq_tail_of_left e hd]; exact he.tail_mem

















theorem kc2_extremeCell_notMem_of_right {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e)
    (hd : e.dir = ![1, 0]) :
    (![dartFace e 0 + 1, dartFace e 1] : Site 2) ∉ K := by
  have h := (npd_corners_right he hd).2
  unfold npd_P10 at h
  exact h



















theorem kc2_extremeCell_dichotomy {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e)
    (hv : (dartFace e) 0 = (dartFace (dartNext K e)) 0) :
    (e.dir = ![-1, 0] ∧ (![dartFace e 0 + 1, dartFace e 1 + 1] : Site 2) ∈ K) ∨
    (e.dir = ![1, 0] ∧ (![dartFace e 0 + 1, dartFace e 1] : Site 2) ∉ K) := by
  rcases kc2_vertStep_dir e hv with hd | hd
  · exact Or.inr ⟨hd, kc2_extremeCell_notMem_of_right he hd⟩
  · exact Or.inl ⟨hd, kc2_extremeCell_mem_of_left he hd⟩

end Walls

end StatMech

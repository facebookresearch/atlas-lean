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

open Set SimpleGraph

namespace StatMech

namespace Walls

open StatMech.Lattice










theorem kc2_dartDir_cases (e : Dart) :
    e.dir = ![1, 0] ∨ e.dir = ![-1, 0] ∨ e.dir = ![0, 1] ∨ e.dir = ![0, -1] :=
  dartDir_cases e









theorem kc2_etaExpand_site2 (z : Site 2) : z = ![z 0, z 1] := by
  funext i; fin_cases i <;> rfl












theorem kc2_dartFace_eq_tail_of_dir_right (e : Dart) (hd : e.dir = ![1, 0]) :
    dartFace e = e.tail := by
  rw [dartFace_of_dir_right e hd, ← kc2_etaExpand_site2]







theorem kc2_rightDart_face_mem_of_tail_mem (K : Set (Site 2)) (e : Dart)
    (hd : e.dir = ![1, 0]) (htail : e.tail ∈ K) :
    dartFace e ∈ K := by
  rw [kc2_dartFace_eq_tail_of_dir_right e hd]; exact htail







theorem kc2_rightDart_face_mem_K (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) (hd : e.dir = ![1, 0]) :
    dartFace e ∈ K :=
  kc2_rightDart_face_mem_of_tail_mem K e hd he.tail_mem














theorem kc2_rightDart_supportOdd_in_K (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) (hd : e.dir = ![1, 0]) (P : Prop) :
    P → dartFace e ∈ K :=
  fun _ => kc2_rightDart_face_mem_K K e he hd

end Walls

end StatMech

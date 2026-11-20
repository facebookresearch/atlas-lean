/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.TurningNumber
import Code.Lattice.CornerBalance
import Code.Lattice.EarExistence

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice

















noncomputable def jc10_cornerInsideCell (e : Dart) : Site 2 := e.tail

@[simp] theorem jc10_cornerInsideCell_def (e : Dart) :
    jc10_cornerInsideCell e = e.tail := rfl






theorem jc10_cornerInsideCell_mem (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e) :
    jc10_cornerInsideCell e ∈ K :=
  he.tail_mem











theorem jc10_convexCorner_front_nmem (K : Set (Site 2)) (e : Dart) (h : turnZ K e = -1) :
    e.head + (-rot90Fun e.dir) ∉ K := by
  classical
  unfold turnZ at h
  by_contra hmem
  rw [if_pos hmem] at h
  norm_num at h





theorem jc10_convexCorner_side_nmem (K : Set (Site 2)) (e : Dart) (h : turnZ K e = -1) :
    e.tail + (-rot90Fun e.dir) ∉ K := by
  classical
  unfold turnZ at h
  by_contra hmem
  split_ifs at h






theorem jc10_convexCorner_unique_insideCell (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) (hturn : turnZ K e = -1) :
    jc10_cornerInsideCell e ∈ K ∧
      e.head + (-rot90Fun e.dir) ∉ K ∧ e.tail + (-rot90Fun e.dir) ∉ K :=
  ⟨jc10_cornerInsideCell_mem K e he,
   jc10_convexCorner_front_nmem K e hturn,
   jc10_convexCorner_side_nmem K e hturn⟩













theorem jc10_exists_convex_corner_insideCell_mem (K : Set (Site 2)) (hK : K.Finite)
    (hne : K.Nonempty) :
    ∃ e : Dart, IsBoundaryDart K e ∧ turnZ K e = -1 ∧
      jc10_cornerInsideCell e ∈ K ∧
      e.head + (-rot90Fun e.dir) ∉ K ∧ e.tail + (-rot90Fun e.dir) ∉ K := by
  obtain ⟨e, hbd, hturn⟩ := exists_convex_corner_dart K hK hne
  exact ⟨e, hbd, hturn, jc10_convexCorner_unique_insideCell K e hbd hturn⟩











theorem jc10_extremeCell_insideCell_eq (c : Site 2) :
    jc10_cornerInsideCell (leftDart c) = c := by
  rw [jc10_cornerInsideCell_def, leftDart_tail]





theorem jc10_extremeCell_insideCell_mem (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    jc10_cornerInsideCell (leftDart c) ∈ K := by
  rw [jc10_extremeCell_insideCell_eq]; exact hc.mem










theorem jc10_unitCell_insideCell_mem :
    jc10_cornerInsideCell ucDart0 ∈ unitCell := by
  rw [jc10_cornerInsideCell_def, ucDart0_tail]
  exact origin_mem_unitCell




theorem jc10_unitCell_convexCorner_unique_insideCell :
    jc10_cornerInsideCell ucDart0 ∈ unitCell ∧
      ucDart0.head + (-rot90Fun ucDart0.dir) ∉ unitCell ∧
      ucDart0.tail + (-rot90Fun ucDart0.dir) ∉ unitCell :=
  jc10_convexCorner_unique_insideCell unitCell ucDart0 ucDart0_boundary ucDart0_turnZ





























end Walls

end StatMech

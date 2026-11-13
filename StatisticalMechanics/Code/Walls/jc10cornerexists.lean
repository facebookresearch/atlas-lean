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
import Code.Lattice.TurningNumber
import Code.Lattice.EarExistence

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice
















theorem jc10_extremeCell_leftDart_convex_corner (K : Set (Site 2)) (c : Site 2)
    (hc : IsExtremeCell K c) :
    IsBoundaryDart K (leftDart c) ∧ turnZ K (leftDart c) = -1 :=
  ⟨extremeCell_boundary K c hc, extremeCell_turnZ K c hc⟩







theorem jc10_exists_extremeCell_convex_corner (K : Set (Site 2)) (hK : K.Finite)
    (hne : K.Nonempty) :
    ∃ c : Site 2, IsExtremeCell K c ∧
      IsBoundaryDart K (leftDart c) ∧ turnZ K (leftDart c) = -1 := by
  obtain ⟨c, hc⟩ := exists_extremeCell K hK hne
  exact ⟨c, hc, jc10_extremeCell_leftDart_convex_corner K c hc⟩









theorem jc10_corner_exists (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ e : Dart, IsBoundaryDart K e ∧ turnZ K e = -1 := by
  obtain ⟨c, _, hbd, hturn⟩ := jc10_exists_extremeCell_convex_corner K hK hne
  exact ⟨leftDart c, hbd, hturn⟩











theorem jc10_nonempty_of_boundaryDart (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e) :
    K.Nonempty :=
  ⟨e.tail, he.tail_mem⟩








theorem jc10_corner_exists_iff_nonempty (K : Set (Site 2)) (hK : K.Finite) :
    (∃ e : Dart, IsBoundaryDart K e ∧ turnZ K e = -1) ↔ K.Nonempty := by
  constructor
  · rintro ⟨e, he, _⟩
    exact jc10_nonempty_of_boundaryDart K e he
  · intro hne
    exact jc10_corner_exists K hK hne

end Walls

end StatMech

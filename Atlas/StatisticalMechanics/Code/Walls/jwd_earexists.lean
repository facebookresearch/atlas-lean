/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































import Mathlib
import Code.Lattice.EarExistence

open SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice














structure jwd_ExtremeEar (K : Set (Site 2)) (c : Site 2) : Prop where
  
  isExtreme : IsExtremeCell K c
  
  isBoundary : IsBoundaryDart K (leftDart c)
  
  turnLeft : turnZ K (leftDart c) = -1





theorem jwd_extremeCell_isEar (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    jwd_ExtremeEar K c where
  isExtreme := hc
  isBoundary := extremeCell_boundary K c hc
  turnLeft := extremeCell_turnZ K c hc












theorem jwd_earExists (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ c, jwd_ExtremeEar K c := by
  obtain ⟨c, hc⟩ := exists_extremeCell K hK hne
  exact ⟨c, jwd_extremeCell_isEar K c hc⟩





theorem jwd_exists_convex_corner_dart (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ e : Dart, IsBoundaryDart K e ∧ turnZ K e = -1 := by
  obtain ⟨c, hear⟩ := jwd_earExists K hK hne
  exact ⟨leftDart c, hear.isBoundary, hear.turnLeft⟩






theorem jwd_earExists_explicit (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ c, c ∈ K ∧ IsBoundaryDart K (leftDart c) ∧ turnZ K (leftDart c) = -1 ∧
      (∀ v ∈ K, lexKey v ≤ lexKey c) := by
  obtain ⟨c, hear⟩ := jwd_earExists K hK hne
  exact ⟨c, hear.isExtreme.mem, hear.isBoundary, hear.turnLeft, hear.isExtreme.maximal⟩









theorem jwd_unitCell_earExists : ∃ c, jwd_ExtremeEar unitCell c :=
  jwd_earExists unitCell unitCell_finite ⟨_, origin_mem_unitCell⟩

end Walls

end StatMech

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
import Code.Lattice.EarExistence
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.JordanExteriorClosure
import Code.Walls.jc10core
import Code.Walls.jc11core

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice














theorem kc6_topWallCount_eq_one (K : Set (Site 2)) (hK : K.Finite) (c : Site 2)
    (hc : IsExtremeCell K c) :
    jc10core_topWallCount c (mpl_orbitLoop K (extremeBase K c hc)) = 1 :=
  jc11_topWallCount_eq_one K hK c hc






theorem kc6_topWallOdd (K : Set (Site 2)) (hK : K.Finite) (c : Site 2) (hc : IsExtremeCell K c) :
    jc10core_TopWallOdd K (extremeBase K c hc) c :=
  jc11_TopWallOdd K hK c hc
















theorem kc6_cornerCellOdd (K : Set (Site 2)) (hK : K.Finite) (c : Site 2) (hc : IsExtremeCell K c) :
    ¬ Even (jec_rayCount c (mpl_orbitLoop K (extremeBase K c hc))) :=
  jc10core_cornerCellOdd_of_topWallOdd K (extremeBase K c hc) c hc (kc6_topWallOdd K hK c hc)





theorem kc6_cornerCellOdd_of_topWallOdd (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (c : Site 2) (hc : IsExtremeCell K c)
    (htop : jc10core_TopWallOdd K a c) :
    ¬ Even (jec_rayCount c (mpl_orbitLoop K a)) :=
  jc10core_cornerCellOdd_of_topWallOdd K a c hc htop











theorem kc6_exists_windingWitness (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ c : Site 2, ∃ hc : IsExtremeCell K c,
      c ∈ K ∧ ¬ Even (jec_rayCount c (mpl_orbitLoop K (extremeBase K c hc))) := by
  obtain ⟨c, hc⟩ := exists_extremeCell K hK hne
  exact ⟨c, hc, hc.mem, kc6_cornerCellOdd K hK c hc⟩











theorem kc6_unitCell_isExtremeCell : IsExtremeCell unitCell (![0, 0] : Site 2) where
  mem := origin_mem_unitCell
  maximal := by
    intro v hv
    rw [unitCell, Set.mem_singleton_iff] at hv
    rw [hv]




theorem kc6_unitCell_cornerCellOdd :
    ¬ Even (jec_rayCount (![0, 0] : Site 2)
      (mpl_orbitLoop unitCell (extremeBase unitCell (![0, 0] : Site 2) kc6_unitCell_isExtremeCell))) :=
  kc6_cornerCellOdd unitCell unitCell_finite (![0, 0] : Site 2) kc6_unitCell_isExtremeCell

end Walls

end StatMech

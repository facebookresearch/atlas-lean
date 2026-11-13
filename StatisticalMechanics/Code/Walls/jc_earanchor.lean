/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































import Mathlib
import Code.Walls.jwd_earexists
import Code.Lattice.EarExistence
import Code.Lattice.EarContraction

open SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice











theorem jc_extremeCell_up_nmem (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    c + ![0, 1] ∉ K :=
  extremeCell_up_nmem K c hc



theorem jc_extremeCell_left_nmem (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    c + ![-1, 0] ∉ K :=
  extremeCell_left_nmem K c hc







theorem jc_extremeCell_neighbor_right_or_down (K : Set (Site 2)) (c v : Site 2)
    (hc : IsExtremeCell K c) (hv : v ∈ K) (hadj : (hypercubicLattice 2).Adj v c) :
    v = c + ![1, 0] ∨ v = c + ![0, -1] :=
  extremeCell_neighbor_right_or_down K c v hc hv hadj



















structure jc_EarAnchor (K : Set (Site 2)) (c : Site 2) : Prop where
  
  isExtreme : IsExtremeCell K c
  
  isBoundary : IsBoundaryDart K (leftDart c)
  
  turnLeft : turnZ K (leftDart c) = -1
  
  neighbor_right_or_down :
    ∀ v ∈ K, (hypercubicLattice 2).Adj v c → v = c + ![1, 0] ∨ v = c + ![0, -1]






theorem jc_extremeCell_isAnchor (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    jc_EarAnchor K c where
  isExtreme := hc
  isBoundary := extremeCell_boundary K c hc
  turnLeft := extremeCell_turnZ K c hc
  neighbor_right_or_down := fun v hv hadj =>
    jc_extremeCell_neighbor_right_or_down K c v hc hv hadj




theorem jc_earAnchor_isEar {K : Set (Site 2)} {c : Site 2} (h : jc_EarAnchor K c) :
    jwd_ExtremeEar K c where
  isExtreme := h.isExtreme
  isBoundary := h.isBoundary
  turnLeft := h.turnLeft















theorem jc_earAnchor (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ c, jc_EarAnchor K c := by
  obtain ⟨c, hc⟩ := exists_extremeCell K hK hne
  exact ⟨c, jc_extremeCell_isAnchor K c hc⟩






theorem jc_earAnchor_explicit (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ c, c ∈ K ∧ IsBoundaryDart K (leftDart c) ∧ turnZ K (leftDart c) = -1 ∧
      (∀ v ∈ K, lexKey v ≤ lexKey c) ∧
      (∀ v ∈ K, (hypercubicLattice 2).Adj v c → v = c + ![1, 0] ∨ v = c + ![0, -1]) := by
  obtain ⟨c, hanchor⟩ := jc_earAnchor K hK hne
  exact ⟨c, hanchor.isExtreme.mem, hanchor.isBoundary, hanchor.turnLeft,
    hanchor.isExtreme.maximal, hanchor.neighbor_right_or_down⟩










theorem jc_unitCell_earAnchor : ∃ c, jc_EarAnchor unitCell c :=
  jc_earAnchor unitCell unitCell_finite ⟨_, origin_mem_unitCell⟩

end Walls

end StatMech

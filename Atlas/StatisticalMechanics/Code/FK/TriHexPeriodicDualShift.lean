/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexPeriodicDual










open SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem triangularIndexedEdge_add (z : Site 2) (a : TriHexEdgeIndex) :
    triangularIndexedEdge (a.1 + z, a.2) =
      Sym2.map (siteTranslate z) (triangularIndexedEdge a) := by
  apply Sym2.eq_iff.mpr
  left
  constructor
  · rfl
  · ext i
    simp [siteTranslate_apply, add_comm, add_left_comm]


theorem hexagonalIndexedEdge_add (z : Site 2) (a : TriHexEdgeIndex) :
    hexagonalIndexedEdge (a.1 + z, a.2) =
      Sym2.map (hexTranslate z) (hexagonalIndexedEdge a) := by
  apply Sym2.eq_iff.mpr
  left
  constructor
  · rfl
  · apply Prod.ext
    · ext i
      simp [hexTranslate_apply, add_comm, add_left_comm]
    · rfl



theorem triHexIndexEquiv_add (z : Site 2) (a : TriHexEdgeIndex) :
    triHexIndexEquiv (a.1 + z, a.2) =
      ((triHexIndexEquiv a).1 + z, (triHexIndexEquiv a).2) := by
  rcases a with ⟨x, i⟩
  fin_cases i <;>
    exact Prod.ext (by
      funext j
      simp [triHexIndexEquiv] <;> ring) rfl



theorem triHexDualEdgeEquiv_add_chart (z : Site 2) (a : TriHexEdgeIndex) :
    ((triHexDualEdgeEquiv
          (triangularEdgeChart (a.1 + z, a.2)) :
        hexagonalGraph.edgeSet) : Sym2 HexVertex) =
      Sym2.map (hexTranslate z)
        ((triHexDualEdgeEquiv (triangularEdgeChart a) :
          hexagonalGraph.edgeSet) : Sym2 HexVertex) := by
  rw [triHexDualEdgeEquiv_chart, triHexDualEdgeEquiv_chart]
  rw [triHexIndexEquiv_add]
  exact hexagonalIndexedEdge_add z (triHexIndexEquiv a)



noncomputable def triangularEdgeTranslate (z : Site 2)
    (e : triangularGraph.edgeSet) : triangularGraph.edgeSet :=
  let a := triangularEdgeChartEquiv.symm e
  triangularEdgeChart (a.1 + z, a.2)

theorem triangularEdgeTranslate_val (z : Site 2)
    (e : triangularGraph.edgeSet) :
    ((triangularEdgeTranslate z e : triangularGraph.edgeSet) : Sym2 (Site 2)) =
      Sym2.map (siteTranslate z) (e : Sym2 (Site 2)) := by
  let a := triangularEdgeChartEquiv.symm e
  have he : triangularEdgeChart a = e :=
    triangularEdgeChartEquiv.apply_symm_apply e
  change triangularIndexedEdge (a.1 + z, a.2) =
    Sym2.map (siteTranslate z) (e : Sym2 (Site 2))
  rw [triangularIndexedEdge_add]
  exact congrArg (Sym2.map (siteTranslate z)) (congrArg Subtype.val he)



noncomputable def hexagonalEdgeTranslate (z : Site 2)
    (e : hexagonalGraph.edgeSet) : hexagonalGraph.edgeSet :=
  let a := hexagonalEdgeChartEquiv.symm e
  hexagonalEdgeChart (a.1 + z, a.2)

theorem hexagonalEdgeTranslate_val (z : Site 2)
    (e : hexagonalGraph.edgeSet) :
    ((hexagonalEdgeTranslate z e : hexagonalGraph.edgeSet) : Sym2 HexVertex) =
      Sym2.map (hexTranslate z) (e : Sym2 HexVertex) := by
  let a := hexagonalEdgeChartEquiv.symm e
  have he : hexagonalEdgeChart a = e :=
    hexagonalEdgeChartEquiv.apply_symm_apply e
  change hexagonalIndexedEdge (a.1 + z, a.2) =
    Sym2.map (hexTranslate z) (e : Sym2 HexVertex)
  rw [hexagonalIndexedEdge_add]
  exact congrArg (Sym2.map (hexTranslate z)) (congrArg Subtype.val he)



theorem triHexDualEdgeEquiv_add (z : Site 2)
    (e : triangularGraph.edgeSet) :
    triHexDualEdgeEquiv (triangularEdgeTranslate z e) =
      hexagonalEdgeTranslate z (triHexDualEdgeEquiv e) := by
  let a := triangularEdgeChartEquiv.symm e
  have he : triangularEdgeChart a = e :=
    triangularEdgeChartEquiv.apply_symm_apply e
  apply Subtype.ext
  change ((triHexDualEdgeEquiv
      (triangularEdgeChart (a.1 + z, a.2)) :
        hexagonalGraph.edgeSet) : Sym2 HexVertex) = _
  rw [triHexDualEdgeEquiv_add_chart]
  rw [he]
  exact (hexagonalEdgeTranslate_val z (triHexDualEdgeEquiv e)).symm

end StatMech.FK.PeriodicPlanar

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexPairOrbitCharts
import Code.FK.TriHexCoarseGeometry
import Code.FK.PeriodicPlanarDualPair









open MeasureTheory Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice



noncomputable def triHexPeriodicPlanarDualPair_of_infiniteVolumeDuality
    (hfreeWired : ∀ {p q : ℝ}
      (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q),
      hexagonal.wiredBufferedInfiniteVolume
          (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).1
          (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).2
          (zero_lt_one.trans_le hq) =
        (triangular.freeBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq)).map
          (continuous_dualConfigEquiv
            triHexFullDualEdgeEquiv).measurable.aemeasurable)
    (hwiredFree : ∀ {p q : ℝ}
      (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q),
      hexagonal.freeBufferedInfiniteVolume
          (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).1
          (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).2
          (zero_lt_one.trans_le hq) =
        (triangular.wiredBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq)).map
          (continuous_dualConfigEquiv
            triHexFullDualEdgeEquiv).measurable.aemeasurable) :
    PeriodicPlanarDualPair triangular hexagonal where
  primalEmbedding := triangularPeriodicPlaneEmbedding
  dualEmbedding := hexagonalPeriodicPlaneEmbedding
  coordinates_eq := rfl
  primal_connected := triangularGraph_connected
  dual_connected := hexagonalGraph_connected
  edgeDual := triHexFullDualEdgeEquiv
  edgeDual_mem_edgeSet := triHexFullDualEdgeEquiv_mem_edgeSet
  edgeDual_shift := triHexFullDualEdgeEquiv_shift
  edgeDual_crossing := by
    intro x y a b hxy hab hdual
    apply (triHexStraightEdge_crossing_iff_dual hxy hab).2
    apply Subtype.ext
    rw [← triHexFullDualEdgeEquiv_eq_edgeDual ⟨s(x, y), hxy⟩]
    exact hdual
  edgeDual_of_crossing := by
    intro x y a b hxy hab t u hcross
    have hold := (triHexStraightEdge_crossing_iff_dual hxy hab).1
      ⟨t, u, hcross⟩
    calc
      triHexFullDualEdgeEquiv s(x, y) =
          (triHexDualEdgeEquiv ⟨s(x, y), hxy⟩ : Sym2 HexVertex) :=
        triHexFullDualEdgeEquiv_eq_edgeDual ⟨s(x, y), hxy⟩
      _ = s(a, b) := congrArg Subtype.val hold
  free_wired_infiniteVolume_dual_law := hfreeWired
  wired_free_infiniteVolume_dual_law := hwiredFree

end StatMech.FK.PeriodicPlanar

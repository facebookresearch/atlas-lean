/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWAxisGapFiniteGraph
import Code.Universality.RSWConnectorActualSelectedObstruction





open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section



theorem rlc_scaleTwoDoubleFailure_axisGapEdges_ne_empty :
    rlc_axisGapEdges rlc_scaleTwoDoubleFailureGap ≠ ∅ := by
  intro hempty
  have hfirst : rlc_scaleTwoDoubleFailureGap.firstEdge ∈
      rlc_axisGapEdges rlc_scaleTwoDoubleFailureGap := by
    simp [rlc_axisGapEdges]
  rw [hempty] at hfirst
  simp at hfirst



theorem rlc_scaleTwoDoubleFailure_axisGapFiniteGraph_has_edge :
    ∃ x y : RlcConnectorVertex 2,
      (rlc_axisGapFiniteGraph rlc_scaleTwoDoubleFailureGap).Adj x y := by
  exact ⟨⟨rlc_scaleTwoDoubleFailureGap.lowerVertex, by
      simpa [rlc_connectorBox] using
        rlc_scaleTwoDoubleFailureGap.lowerVertex_mem_connectorBox⟩,
    ⟨rlc_scaleTwoDoubleFailureGap.seedVertex, by
      simpa [rlc_connectorBox] using
        rlc_scaleTwoDoubleFailureGap.seedVertex_mem_connectorBox⟩,
    rlc_scaleTwoDoubleFailureGap.firstEdge_mem_axisGapFiniteGraph⟩



theorem rlc_scaleTwoDoubleFailure_axisGapFiniteGraph_ne_connectorFiniteGraph :
    rlc_axisGapFiniteGraph rlc_scaleTwoDoubleFailureGap ≠
      rlc_connectorFiniteGraph rlc_scaleTwoDoubleFailureRight
        rlc_scaleTwoDoubleFailureLeft := by
  rintro heq
  obtain ⟨x, y, hxy⟩ :=
    rlc_scaleTwoDoubleFailure_axisGapFiniteGraph_has_edge
  rw [heq] at hxy
  exact (by
    simpa [rlc_connectorFiniteGraph,
      rlc_scaleTwoDoubleFailure_connectorEdges_eq_empty] using hxy)

end

end StatMech.Universality

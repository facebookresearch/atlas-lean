/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWShiftedEndpoint














open Function MeasureTheory Set

namespace StatMech
namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box



theorem rlc_right_start_shiftedPreimage_not_mem_of_bottom {n : ℤ}
    (gamma : RlcRightDiagonalPath n)
    (hbottom : (gamma.1.1 : Site 2) 1 = -n) :
    rlc_shiftedEndpointPreimage (gamma.1.1 : Site 2) ∉
      rlc_pathVertices gamma.1 := by
  intro hmem
  have hrect := rlc_pathVertex_mem_rect gamma.1 hmem
  rw [mem_rect] at hrect
  simp only [rlc_shiftedEndpointPreimage_one] at hrect
  omega



theorem rlc_not_shiftedEndpointTraceNeighbors_of_right_start_bottom {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hbottom : (gamma.1.1 : Site 2) 1 = -n) :
    ¬ RlcShiftedEndpointTraceNeighbors gamma gamma' := by
  intro h
  exact (rlc_right_start_shiftedPreimage_not_mem_of_bottom gamma hbottom)
    h.right_start_mem_right

private def rlc_sen_v0 : rect 0 2 (-1) 1 :=
  ⟨![0, -1], by simp [mem_rect]⟩

private def rlc_sen_v1 : rect 0 2 (-1) 1 :=
  ⟨![1, -1], by simp [mem_rect]⟩

private def rlc_sen_v2 : rect 0 2 (-1) 1 :=
  ⟨![2, -1], by simp [mem_rect]⟩

private def rlc_sen_v3 : rect 0 2 (-1) 1 :=
  ⟨![2, 0], by simp [mem_rect]⟩

private theorem rlc_sen_adj01 :
    ((hypercubicLattice 2).induce (rect 0 2 (-1) 1)).Adj
      rlc_sen_v0 rlc_sen_v1 := by
  simp [rlc_sen_v0, rlc_sen_v1, hypercubicLattice_adj]

private theorem rlc_sen_adj12 :
    ((hypercubicLattice 2).induce (rect 0 2 (-1) 1)).Adj
      rlc_sen_v1 rlc_sen_v2 := by
  simp [rlc_sen_v1, rlc_sen_v2, hypercubicLattice_adj]

private theorem rlc_sen_adj23 :
    ((hypercubicLattice 2).induce (rect 0 2 (-1) 1)).Adj
      rlc_sen_v2 rlc_sen_v3 := by
  simp [rlc_sen_v2, rlc_sen_v3, hypercubicLattice_adj]

private def rlc_sen_walk :
    ((hypercubicLattice 2).induce (rect 0 2 (-1) 1)).Walk
      rlc_sen_v0 rlc_sen_v3 :=
  .cons rlc_sen_adj01 (.cons rlc_sen_adj12 (.cons rlc_sen_adj23 .nil))



noncomputable def rlc_shiftedNeighborCounterexampleRight :
    RlcRightDiagonalPath 1 := by
  let x : leftSide 0 2 (-1) 1 :=
    ⟨(rlc_sen_v0 : Site 2), by simp [rlc_sen_v0, mem_leftSide, mem_rect]⟩
  let y : rightSide 0 2 (-1) 1 :=
    ⟨(rlc_sen_v3 : Site 2), by simp [rlc_sen_v3, mem_rightSide, mem_rect]⟩
  let gamma : RlcCrossingPath 0 2 (-1) 1 :=
    ⟨x, y, rlc_sen_walk.toPath⟩
  exact ⟨gamma, by simp [gamma, x, rlc_sen_v0, rlc_lowerHalf],
    by simp [gamma, y, rlc_sen_v3, rlc_upperHalf]⟩

@[simp] theorem rlc_shiftedNeighborCounterexampleRight_start_one :
    (rlc_shiftedNeighborCounterexampleRight.1.1 : Site 2) 1 = -1 := by
  simp [rlc_shiftedNeighborCounterexampleRight, rlc_sen_v0]



theorem rlc_shiftedEndpointTraceNeighbors_counterexample :
    ¬ RlcShiftedEndpointTraceNeighbors
      rlc_shiftedNeighborCounterexampleRight
      (rlc_rot180RightPath rlc_shiftedNeighborCounterexampleRight) := by
  apply rlc_not_shiftedEndpointTraceNeighbors_of_right_start_bottom
  exact rlc_shiftedNeighborCounterexampleRight_start_one

end Universality
end StatMech

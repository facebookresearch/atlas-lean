/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWReflectedRegion

















open Function MeasureTheory Set

namespace StatMech
namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box


abbrev rlc_shiftedEndpointPreimage (x : Site 2) : Site 2 :=
  rlc_primalDualReflect.symm x

@[simp] theorem rlc_shiftedEndpointPreimage_zero (x : Site 2) :
    rlc_shiftedEndpointPreimage x 0 = -x 0 := rfl

@[simp] theorem rlc_shiftedEndpointPreimage_one (x : Site 2) :
    rlc_shiftedEndpointPreimage x 1 = x 1 - 1 := rfl




def RlcShiftedEndpointTraceSplit {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) : Prop :=
  ((rlc_shiftedEndpointPreimage (gamma.1.1 : Site 2) ∈
        rlc_pathVertices gamma.1 ∧
      rlc_shiftedEndpointPreimage (gamma.1.2.1 : Site 2) ∈
        rlc_pathVertices gamma'.1) ∨
    (rlc_shiftedEndpointPreimage (gamma.1.1 : Site 2) ∈
        rlc_pathVertices gamma'.1 ∧
      rlc_shiftedEndpointPreimage (gamma.1.2.1 : Site 2) ∈
        rlc_pathVertices gamma.1)) ∧
  ((rlc_shiftedEndpointPreimage (gamma'.1.1 : Site 2) ∈
        rlc_pathVertices gamma.1 ∧
      rlc_shiftedEndpointPreimage (gamma'.1.2.1 : Site 2) ∈
        rlc_pathVertices gamma'.1) ∨
    (rlc_shiftedEndpointPreimage (gamma'.1.1 : Site 2) ∈
        rlc_pathVertices gamma'.1 ∧
      rlc_shiftedEndpointPreimage (gamma'.1.2.1 : Site 2) ∈
        rlc_pathVertices gamma.1))



theorem rlc_right_end_shiftedPreimage_not_mem_rightPath {n : ℤ}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n) :
    rlc_shiftedEndpointPreimage (gamma.1.2.1 : Site 2) ∉
      rlc_pathVertices gamma.1 := by
  intro h
  have hrect := rlc_pathVertex_mem_rect gamma.1 h
  have hend := gamma.1.2.1.2
  rw [mem_rect] at hrect
  rw [mem_rightSide] at hend
  have hx : (gamma.1.2.1 : Site 2) 0 = 2 * n := hend.2
  have hxLower := hrect.1
  simp only [rlc_shiftedEndpointPreimage_zero] at hxLower
  omega



theorem rlc_left_start_shiftedPreimage_not_mem_leftPath {n : ℤ}
    (hn : 0 < n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_shiftedEndpointPreimage (gamma'.1.1 : Site 2) ∉
      rlc_pathVertices gamma'.1 := by
  intro h
  have hrect := rlc_pathVertex_mem_rect gamma'.1 h
  have hstart := gamma'.1.1.2
  rw [mem_rect] at hrect
  rw [mem_leftSide] at hstart
  have hx : (gamma'.1.1 : Site 2) 0 = -2 * n := hstart.2
  have hxUpper := hrect.2.1
  simp only [rlc_shiftedEndpointPreimage_zero] at hxUpper
  omega




structure RlcShiftedEndpointTraceNeighbors {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) : Prop where
  right_start_mem_right :
    rlc_shiftedEndpointPreimage (gamma.1.1 : Site 2) ∈
      rlc_pathVertices gamma.1
  right_end_mem_left :
    rlc_shiftedEndpointPreimage (gamma.1.2.1 : Site 2) ∈
      rlc_pathVertices gamma'.1
  left_start_mem_right :
    rlc_shiftedEndpointPreimage (gamma'.1.1 : Site 2) ∈
      rlc_pathVertices gamma.1
  left_end_mem_left :
    rlc_shiftedEndpointPreimage (gamma'.1.2.1 : Site 2) ∈
      rlc_pathVertices gamma'.1



theorem rlc_shiftedEndpointTraceNeighbors_iff_coordinates {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcShiftedEndpointTraceNeighbors gamma gamma' ↔
      ![-(gamma.1.1 : Site 2) 0,
          (gamma.1.1 : Site 2) 1 - 1] ∈ rlc_pathVertices gamma.1 ∧
      ![-(gamma.1.2.1 : Site 2) 0,
          (gamma.1.2.1 : Site 2) 1 - 1] ∈ rlc_pathVertices gamma'.1 ∧
      ![-(gamma'.1.1 : Site 2) 0,
          (gamma'.1.1 : Site 2) 1 - 1] ∈ rlc_pathVertices gamma.1 ∧
      ![-(gamma'.1.2.1 : Site 2) 0,
          (gamma'.1.2.1 : Site 2) 1 - 1] ∈
        rlc_pathVertices gamma'.1 := by
  constructor
  · rintro ⟨hr0, hr1, hl0, hl1⟩
    simpa [rlc_shiftedEndpointPreimage,
      rlc_primalDualReflectInvFun] using ⟨hr0, hr1, hl0, hl1⟩
  · rintro ⟨hr0, hr1, hl0, hl1⟩
    constructor
    · simpa [rlc_shiftedEndpointPreimage,
        rlc_primalDualReflectInvFun] using hr0
    · simpa [rlc_shiftedEndpointPreimage,
        rlc_primalDualReflectInvFun] using hr1
    · simpa [rlc_shiftedEndpointPreimage,
        rlc_primalDualReflectInvFun] using hl0
    · simpa [rlc_shiftedEndpointPreimage,
        rlc_primalDualReflectInvFun] using hl1

theorem rlc_shiftedEndpointTraceSplit_iff_neighbors {n : ℤ}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    RlcShiftedEndpointTraceSplit gamma gamma' ↔
      RlcShiftedEndpointTraceNeighbors gamma gamma' := by
  constructor
  · rintro ⟨hr, hl⟩
    have hrightOuter :=
      rlc_right_end_shiftedPreimage_not_mem_rightPath hn gamma
    have hleftOuter :=
      rlc_left_start_shiftedPreimage_not_mem_leftPath hn gamma'
    rcases hr with hr | hr
    · rcases hl with hl | hl
      · exact ⟨hr.1, hr.2, hl.1, hl.2⟩
      · exact False.elim (hleftOuter hl.1)
    · exact False.elim (hrightOuter hr.2)
  · rintro ⟨hr0, hr1, hl0, hl1⟩
    exact ⟨Or.inl ⟨hr0, hr1⟩, Or.inl ⟨hl0, hl1⟩⟩



theorem rlc_reflectedEndpointXor_of_failure_of_shiftedTraceSplit {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
    (hsplit : RlcShiftedEndpointTraceSplit gamma gamma') :
    RlcReflectedEndpointXor gamma gamma'
      (rlc_mixedWiredReachSet G omega) := by
  rw [rlc_reflectedEndpointXor_iff_affine_preimages]
  obtain ⟨hr, hl⟩ := hsplit
  have rightMem {x : Site 2} (hx : x ∈ rlc_pathVertices gamma.1) :
      x ∈ rlc_mixedWiredReachSet G omega :=
    rlc_rightPathVertex_mem_mixedWiredReachSet G omega hx
  have leftNotMem {x : Site 2} (hx : x ∈ rlc_pathVertices gamma'.1) :
      x ∉ rlc_mixedWiredReachSet G omega :=
    rlc_leftPathVertex_not_mem_mixedWiredReachSet_of_failure
      G omega hno hx
  have mem_ne_notMem {P Q : Prop} (hP : P) (hQ : ¬ Q) : P ≠ Q := by
    intro h
    rw [h] at hP
    exact hQ hP
  have notMem_ne_mem {P Q : Prop} (hP : ¬ P) (hQ : Q) : P ≠ Q := by
    intro h
    rw [h] at hP
    exact hP hQ
  constructor
  · rcases hr with hr | hr
    · exact mem_ne_notMem (rightMem hr.1) (leftNotMem hr.2)
    · exact notMem_ne_mem (leftNotMem hr.1) (rightMem hr.2)
  · rcases hl with hl | hl
    · exact mem_ne_notMem (rightMem hl.1) (leftNotMem hl.2)
    · exact notMem_ne_mem (leftNotMem hl.1) (rightMem hl.2)


theorem rlc_reflectedEndpointXor_of_failure_of_shiftedTraceNeighbors {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
    (hneighbors : RlcShiftedEndpointTraceNeighbors gamma gamma') :
    RlcReflectedEndpointXor gamma gamma'
      (rlc_mixedWiredReachSet G omega) := by
  apply rlc_reflectedEndpointXor_of_failure_of_shiftedTraceSplit
    G omega hno
  exact (rlc_shiftedEndpointTraceSplit_iff_neighbors
    hn gamma gamma').2 hneighbors



theorem rlc_mixedWiredConnectorEvent_dualReflect_of_shiftedTraceNeighbors
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
    (hneighbors : RlcShiftedEndpointTraceNeighbors gamma gamma')
    (hregion : rlc_reflectedPrimalRegion
        (rlc_mixedWiredReachSet G omega) =
      jec_leftRegion
        ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
          (rlc_openSubgraph_le_lattice _)))
    (horder : RlcOuterExitContactArcOrder G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  apply rlc_mixedWiredConnectorEvent_dualReflect_of_reflectedRegion_xor
    G hn hlt omega hregion
  · exact rlc_reflectedEndpointXor_of_failure_of_shiftedTraceNeighbors
      G hn omega hno hneighbors
  · exact horder

end Universality
end StatMech

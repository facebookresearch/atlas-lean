/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWContactRedesign
import Code.Universality.RSWReflectedRegion
















open Function MeasureTheory Set

namespace StatMech
namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box




def RlcTracePreimagesSplit {a b c d n : ℤ}
    (gamma : RlcCrossingPath a b c d)
    (right : RlcRightDiagonalPath n) (left : RlcLeftDiagonalPath n) : Prop :=
  ∃ x ∈ rlc_pathVertices gamma, ∃ y ∈ rlc_pathVertices gamma,
    ((rlc_primalDualReflect.symm x ∈ rlc_pathVertices right.1 ∧
        rlc_primalDualReflect.symm y ∈ rlc_pathVertices left.1) ∨
      (rlc_primalDualReflect.symm x ∈ rlc_pathVertices left.1 ∧
        rlc_primalDualReflect.symm y ∈ rlc_pathVertices right.1))




def RlcLowestHighestTracePreimageSplit {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) : Prop :=
  RlcTracePreimagesSplit gamma.1 gamma gamma' ∧
    RlcTracePreimagesSplit gamma'.1 gamma gamma'



def RlcTracePreimageRegionSplit {a b c d : ℤ}
    (gamma : RlcCrossingPath a b c d) (K : Set (Site 2)) : Prop :=
  ∃ x ∈ rlc_pathVertices gamma, ∃ y ∈ rlc_pathVertices gamma,
    ((rlc_primalDualReflect.symm x ∈ K ∧
        rlc_primalDualReflect.symm y ∉ K) ∨
      (rlc_primalDualReflect.symm x ∉ K ∧
        rlc_primalDualReflect.symm y ∈ K))



theorem rlc_tracePreimageRegionSplit_of_failure
    {n a b c d : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
    (tau : RlcCrossingPath a b c d)
    (hsplit : RlcTracePreimagesSplit tau gamma gamma') :
    RlcTracePreimageRegionSplit tau (rlc_mixedWiredReachSet G omega) := by
  obtain ⟨x, hx, y, hy, hxy | hxy⟩ := hsplit
  · exact ⟨x, hx, y, hy, Or.inl
      ⟨rlc_rightPathVertex_mem_mixedWiredReachSet G omega hxy.1,
        rlc_leftPathVertex_not_mem_mixedWiredReachSet_of_failure
          G omega hno hxy.2⟩⟩
  · exact ⟨x, hx, y, hy, Or.inr
      ⟨rlc_leftPathVertex_not_mem_mixedWiredReachSet_of_failure
          G omega hno hxy.1,
        rlc_rightPathVertex_mem_mixedWiredReachSet G omega hxy.2⟩⟩



theorem rlc_traceStraddlesLoop_of_preimageRegionSplit
    {a b c d : ℤ} {u : Site 2}
    (C : (hypercubicLattice 2).Walk u u)
    (gamma : RlcCrossingPath a b c d) (K : Set (Site 2))
    (hregion : rlc_reflectedPrimalRegion K = jec_leftRegion C)
    (hsplit : RlcTracePreimageRegionSplit gamma K) :
    rlc_TraceStraddlesLoop C gamma := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hsplit
  refine ⟨x, hx, y, hy, ?_⟩
  rw [rlc_oppositeLoopSides_iff_leftRegion_xor, ← hregion]
  simpa only [rlc_mem_reflectedPrimalRegion_iff] using hxy





theorem rlc_traceStraddlesLoop_iff_preimageRegionSplit
    {a b c d : ℤ} {u : Site 2}
    (C : (hypercubicLattice 2).Walk u u)
    (gamma : RlcCrossingPath a b c d) (K : Set (Site 2))
    (hregion : rlc_reflectedPrimalRegion K = jec_leftRegion C) :
    rlc_TraceStraddlesLoop C gamma ↔
      RlcTracePreimageRegionSplit gamma K := by
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine ⟨x, hx, y, hy, ?_⟩
    rw [rlc_oppositeLoopSides_iff_leftRegion_xor, ← hregion] at hxy
    simpa only [rlc_mem_reflectedPrimalRegion_iff] using hxy
  · exact rlc_traceStraddlesLoop_of_preimageRegionSplit
      C gamma K hregion




def rlc_outerExitWindingRegion {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) : Set (Site 2) :=
  jec_leftRegion
    ((mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
      (rlc_outerExitAnchor G omega)).mapLe (faceBoundaryGraph_le _))



def RlcOuterExitTraceWindingSplit {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) : Prop :=
  RlcTracePreimageRegionSplit gamma.1
      (rlc_outerExitWindingRegion G omega) ∧
    RlcTracePreimageRegionSplit gamma'.1
      (rlc_outerExitWindingRegion G omega)





theorem rlc_outerExitTraceSeparation_iff_windingSplit
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    RlcOuterExitTraceSeparation G hn hlt omega ↔
      RlcOuterExitTraceWindingSplit G omega := by
  let C := (rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
    (rlc_openSubgraph_le_lattice _)
  have hregion : rlc_reflectedPrimalRegion
        (rlc_outerExitWindingRegion G omega) = jec_leftRegion C := by
    exact rlc_outerExit_reflectedRegion_eq_leftRegion_of_fill_eq
      G hn hlt omega (rlc_outerExitWindingRegion G omega) rfl
  change (rlc_TraceStraddlesLoop C gamma.1 ∧
      rlc_TraceStraddlesLoop C gamma'.1) ↔ _
  exact and_congr
    (rlc_traceStraddlesLoop_iff_preimageRegionSplit C gamma.1 _ hregion)
    (rlc_traceStraddlesLoop_iff_preimageRegionSplit C gamma'.1 _ hregion)






def RlcOuterExitJordanTraceSides {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) : Prop :=
  rlc_mixedWiredReachSet G omega ⊆ rlc_outerExitWindingRegion G omega ∧
    ∀ z ∈ rlc_pathVertices gamma'.1,
      z ∉ rlc_mixedWiredReachSet G omega →
        z ∉ rlc_outerExitWindingRegion G omega




theorem rlc_tracePreimageWindingSplit_of_failure
    {n a b c d : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
    (hJordan : RlcOuterExitJordanTraceSides G omega)
    (tau : RlcCrossingPath a b c d)
    (hsplit : RlcTracePreimagesSplit tau gamma gamma') :
    RlcTracePreimageRegionSplit tau
      (rlc_outerExitWindingRegion G omega) := by
  obtain ⟨x, hx, y, hy, hxy | hxy⟩ := hsplit
  · have hxK := rlc_rightPathVertex_mem_mixedWiredReachSet
      G omega hxy.1
    have hyK := rlc_leftPathVertex_not_mem_mixedWiredReachSet_of_failure
      G omega hno hxy.2
    exact ⟨x, hx, y, hy, Or.inl
      ⟨hJordan.1 hxK, hJordan.2 _ hxy.2 hyK⟩⟩
  · have hxK := rlc_leftPathVertex_not_mem_mixedWiredReachSet_of_failure
      G omega hno hxy.1
    have hyK := rlc_rightPathVertex_mem_mixedWiredReachSet
      G omega hxy.2
    exact ⟨x, hx, y, hy, Or.inr
      ⟨hJordan.2 _ hxy.1 hxK, hJordan.1 hyK⟩⟩



theorem rlc_outerExitJordanTraceSides_of_region_eq {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hregion : rlc_mixedWiredReachSet G omega =
      rlc_outerExitWindingRegion G omega) :
    RlcOuterExitJordanTraceSides G omega := by
  constructor
  · intro z hz
    rwa [← hregion]
  · intro z _hzPath hzK hzRegion
    exact hzK (hregion.symm ▸ hzRegion)




theorem rlc_outerExitTraceSeparation_of_failure_of_preimageSplit
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
    (htrace : RlcLowestHighestTracePreimageSplit gamma gamma')
    (hJordan : RlcOuterExitJordanTraceSides G omega) :
    RlcOuterExitTraceSeparation G hn hlt omega := by
  let C := (rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
    (rlc_openSubgraph_le_lattice _)
  have hregion : rlc_reflectedPrimalRegion
        (rlc_outerExitWindingRegion G omega) = jec_leftRegion C := by
    exact rlc_outerExit_reflectedRegion_eq_leftRegion_of_fill_eq
      G hn hlt omega (rlc_outerExitWindingRegion G omega) rfl
  have hright : RlcTracePreimageRegionSplit gamma.1
      (rlc_outerExitWindingRegion G omega) :=
    rlc_tracePreimageWindingSplit_of_failure
      G omega hno hJordan gamma.1 htrace.1
  have hleft : RlcTracePreimageRegionSplit gamma'.1
      (rlc_outerExitWindingRegion G omega) :=
    rlc_tracePreimageWindingSplit_of_failure
      G omega hno hJordan gamma'.1 htrace.2
  change rlc_TraceStraddlesLoop C gamma.1 ∧
    rlc_TraceStraddlesLoop C gamma'.1
  exact ⟨rlc_traceStraddlesLoop_of_preimageRegionSplit
      C gamma.1 _ hregion hright,
    rlc_traceStraddlesLoop_of_preimageRegionSplit
      C gamma'.1 _ hregion hleft⟩




theorem rlc_mixedWiredConnectorEvent_dualReflect_of_failure_of_preimageSplit
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
    (htrace : RlcLowestHighestTracePreimageSplit gamma gamma')
    (hJordan : RlcOuterExitJordanTraceSides G omega)
    (horder : RlcOuterExitContactArcOrder G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_traceSeparation
    G hn hlt omega
    (rlc_outerExitTraceSeparation_of_failure_of_preimageSplit
      G hn hlt omega hno htrace hJordan)
    horder

end Universality
end StatMech

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWWindingSideObstruction





















open Function MeasureTheory Set

namespace StatMech
namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box




def RlcTraceReflectedBoundaryContact {a b c d : ℤ}
    (tau : RlcCrossingPath a b c d) (K : Set (Site 2)) : Prop :=
  ∃ x y : Site 2, s(x, y) ∈ rlc_pathEdges tau ∧
    bdEdge (rlc_reflectedPrimalRegion K) s(x, y)



def RlcLowestHighestReflectedBoundaryContact {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) : Prop :=
  RlcTraceReflectedBoundaryContact gamma.1
      (rlc_outerExitWindingRegion G omega) ∧
    RlcTraceReflectedBoundaryContact gamma'.1
      (rlc_outerExitWindingRegion G omega)



theorem rlc_ambientCrossingWalk_edge_mem_pathEdges
    {a b c d : ℤ} (tau : RlcCrossingPath a b c d)
    {e : Sym2 (Site 2)}
    (he : e ∈ (rlc_ambientCrossingWalk tau).edges) :
    e ∈ rlc_pathEdges tau := by
  let hom : ((hypercubicLattice 2).induce (rect a b c d)) →g
      hypercubicLattice 2 :=
    (SimpleGraph.Embedding.induce (G := hypercubicLattice 2)
      (rect a b c d)).toHom
  let p : ((hypercubicLattice 2).induce (rect a b c d)).Walk _ _ :=
    tau.2.2.1
  change e ∈ (p.map hom).edges at he
  rw [SimpleGraph.Walk.edges_map hom p] at he
  obtain ⟨f, hf, hfe⟩ := List.mem_map.mp he
  rw [rlc_pathEdges, Finset.mem_image]
  refine ⟨f, ?_, ?_⟩
  · simpa [p] using hf
  · simpa [hom] using hfe





theorem rlc_tracePreimageRegionSplit_iff_reflectedBoundaryContact
    {a b c d : ℤ} (tau : RlcCrossingPath a b c d)
    (K : Set (Site 2)) :
    RlcTracePreimageRegionSplit tau K ↔
      RlcTraceReflectedBoundaryContact tau K := by
  constructor
  · rintro ⟨x, hxPath, y, hyPath, hxy⟩
    let W := rlc_ambientCrossingWalk tau
    have hxW : x ∈ W.support :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices tau x).2 hxPath
    have hyW : y ∈ W.support :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices tau y).2 hyPath
    have boundary_of_sides {u v : Site 2}
        (huW : u ∈ W.support) (hvW : v ∈ W.support)
        (hu : rlc_primalDualReflect.symm u ∈ K)
        (hv : rlc_primalDualReflect.symm v ∉ K) :
        RlcTraceReflectedBoundaryContact tau K := by
      let wuv : (hypercubicLattice 2).Walk u v :=
        (W.takeUntil u huW).reverse.append (W.takeUntil v hvW)
      have huRef : u ∈ rlc_reflectedPrimalRegion K := by
        rw [rlc_mem_reflectedPrimalRegion_iff]
        exact hu
      have hvRef : v ∉ rlc_reflectedPrimalRegion K := by
        rw [rlc_mem_reflectedPrimalRegion_iff]
        exact hv
      obtain ⟨p, q, hpqBoundary, hpqEdge⟩ :=
        rlc_walk_mem_edgeBoundary_edges
          (rlc_reflectedPrimalRegion K) wuv huRef hvRef
      have hpqW : s(p, q) ∈ W.edges := by
        dsimp only [wuv] at hpqEdge
        rw [SimpleGraph.Walk.edges_append,
          SimpleGraph.Walk.edges_reverse, List.mem_append,
          List.mem_reverse] at hpqEdge
        rcases hpqEdge with hpqEdge | hpqEdge
        · exact W.edges_takeUntil_subset huW hpqEdge
        · exact W.edges_takeUntil_subset hvW hpqEdge
      refine ⟨p, q, rlc_ambientCrossingWalk_edge_mem_pathEdges tau hpqW, ?_⟩
      rw [bdEdge_mk]
      exact hpqBoundary.2
    rcases hxy with hxy | hxy
    · exact boundary_of_sides hxW hyW hxy.1 hxy.2
    · exact boundary_of_sides hyW hxW hxy.2 hxy.1
  · rintro ⟨x, y, hxyPath, hxyBoundary⟩
    have hvertices := rlc_pathEdge_endpoints_mem_vertices tau hxyPath
    rw [bdEdge_mk, rlc_mem_reflectedPrimalRegion_iff,
      rlc_mem_reflectedPrimalRegion_iff] at hxyBoundary
    by_cases hx : rlc_primalDualReflect.symm x ∈ K
    · exact ⟨x, hvertices.1, y, hvertices.2,
        Or.inl ⟨hx, hxyBoundary.mp hx⟩⟩
    · have hy : rlc_primalDualReflect.symm y ∈ K := by
        by_contra hy
        exact hx (hxyBoundary.mpr hy)
      exact ⟨x, hvertices.1, y, hvertices.2, Or.inr ⟨hx, hy⟩⟩



theorem rlc_outerExitTraceWindingSplit_iff_reflectedBoundaryContact
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) :
    RlcOuterExitTraceWindingSplit G omega ↔
      RlcLowestHighestReflectedBoundaryContact G omega := by
  exact and_congr
    (rlc_tracePreimageRegionSplit_iff_reflectedBoundaryContact
      gamma.1 (rlc_outerExitWindingRegion G omega))
    (rlc_tracePreimageRegionSplit_iff_reflectedBoundaryContact
      gamma'.1 (rlc_outerExitWindingRegion G omega))



theorem rlc_outerExitTraceSeparation_of_reflectedBoundaryContact
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hcontact : RlcLowestHighestReflectedBoundaryContact G omega) :
    RlcOuterExitTraceSeparation G hn hlt omega := by
  rw [rlc_outerExitTraceSeparation_iff_windingSplit,
    rlc_outerExitTraceWindingSplit_iff_reflectedBoundaryContact]
  exact hcontact



theorem rlc_mixedWiredConnectorEvent_dualReflect_of_boundaryContact
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hcontact : RlcLowestHighestReflectedBoundaryContact G omega)
    (horder : RlcOuterExitContactArcOrder G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_traceSeparation
    G hn hlt omega
    (rlc_outerExitTraceSeparation_of_reflectedBoundaryContact
      G hn hlt omega hcontact)
    horder




theorem rlc_windingSideCounterexample_not_reflectedBoundaryContact :
    ¬ RlcLowestHighestReflectedBoundaryContact
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig := by
  rw [← rlc_outerExitTraceWindingSplit_iff_reflectedBoundaryContact]
  exact rlc_windingSideCounterexample_not_windingSplit

end Universality
end StatMech

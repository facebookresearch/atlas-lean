/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWRayTransport

















open Function MeasureTheory Set

namespace StatMech
namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box



theorem rlc_leftRegion_dualReflect_map {a : Site 2}
    (C : (hypercubicLattice 2).Walk a a) :
    jec_leftRegion (C.map rlc_dualReflectLatticeHom) =
      rlc_reflectedPrimalRegion (jec_leftRegion C) := by
  ext x
  rw [rlc_mem_reflectedPrimalRegion_iff, jec_mem_leftRegion,
    jec_mem_leftRegion]
  have h := rlc_rayParity_dualReflect_map C
    (rlc_primalDualReflect.symm x)
  have hx : rlc_primalDualReflect (rlc_primalDualReflect.symm x) = x := by
    simp
  rw [hx] at h
  exact not_congr h




theorem rlc_reflectedRegion_eq_leftRegion_map_of_eq {a : Site 2}
    (C : (hypercubicLattice 2).Walk a a) (F : Set (Site 2))
    (hF : F = jec_leftRegion C) :
    rlc_reflectedPrimalRegion F =
      jec_leftRegion (C.map rlc_dualReflectLatticeHom) := by
  rw [hF, rlc_leftRegion_dualReflect_map]



theorem rlc_dualReflectOpenWalk_underlying_edges
    (eta : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (w : (openSubgraph 2 (fci_faceDualConfig eta)).Walk x y) :
    ((rlc_dualReflectOpenWalk eta w).mapLe
        (rlc_openSubgraph_le_lattice _)).edges =
      ((w.mapLe (rlc_openSubgraph_le_lattice _)).map
        rlc_dualReflectLatticeHom).edges := by
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
  unfold rlc_dualReflectOpenWalk
  calc
    (w.map (rlc_dualReflectOpenHom eta)).edges =
        List.map (Sym2.map (rlc_dualReflectOpenHom eta)) w.edges :=
      SimpleGraph.Walk.edges_map (rlc_dualReflectOpenHom eta) w
    _ = List.map (Sym2.map rlc_dualReflectLatticeHom) w.edges := by
      apply List.map_congr_left
      intro e _he
      induction e using Sym2.inductionOn with
      | _ u v => rfl
    _ = ((w.mapLe (rlc_openSubgraph_le_lattice _)).map
        rlc_dualReflectLatticeHom).edges := by
      rw [SimpleGraph.Walk.edges_map,
        SimpleGraph.Walk.edges_mapLe_eq_edges]




theorem rlc_outerExitReflectedOpenLoop_edges_eq_map {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    (((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
      (rlc_openSubgraph_le_lattice _)).edges) =
      (((mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
        (rlc_outerExitAnchor G omega)).mapLe
          (faceBoundaryGraph_le _)).map
            rlc_dualReflectLatticeHom).edges := by
  rw [rlc_outerExitReflectedOpenLoop,
    rlc_dualReflectOpenWalk_underlying_edges]
  rw [SimpleGraph.Walk.edges_map,
    SimpleGraph.Walk.edges_mapLe_eq_edges,
    SimpleGraph.Walk.edges_map,
    SimpleGraph.Walk.edges_mapLe_eq_edges]
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges]



theorem rlc_outerExitReflectedOpenLoop_leftRegion_eq_map {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    jec_leftRegion
        ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
          (rlc_openSubgraph_le_lattice _)) =
      jec_leftRegion
        (((mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
          (rlc_outerExitAnchor G omega)).mapLe
            (faceBoundaryGraph_le _)).map
              rlc_dualReflectLatticeHom) := by
  ext x
  simp only [jec_mem_leftRegion, jec_rayCount]
  rw [rlc_outerExitReflectedOpenLoop_edges_eq_map G hn hlt omega]




theorem rlc_outerExit_reflectedRegion_eq_leftRegion_of_fill_eq {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) (F : Set (Site 2))
    (hfill : F = jec_leftRegion
      ((mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
        (rlc_outerExitAnchor G omega)).mapLe
          (faceBoundaryGraph_le _))) :
    rlc_reflectedPrimalRegion F =
      jec_leftRegion
        ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
          (rlc_openSubgraph_le_lattice _)) := by
  rw [rlc_outerExitReflectedOpenLoop_leftRegion_eq_map G hn hlt omega]
  exact rlc_reflectedRegion_eq_leftRegion_map_of_eq _ F hfill



theorem rlc_right_start_mem_reflectedPrimalRegion_iff {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (K : Set (Site 2)) :
    (gamma.1.1 : Site 2) ∈ rlc_reflectedPrimalRegion K ↔
      ![-(gamma.1.1 : Site 2) 0,
        (gamma.1.1 : Site 2) 1 - 1] ∈ K := by
  rw [rlc_mem_reflectedPrimalRegion_iff]
  have h : rlc_primalDualReflect.symm (gamma.1.1 : Site 2) =
      ![-(gamma.1.1 : Site 2) 0, (gamma.1.1 : Site 2) 1 - 1] := by
    ext i
    fin_cases i <;> simp
  rw [h]



theorem rlc_right_end_mem_reflectedPrimalRegion_iff {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (K : Set (Site 2)) :
    (gamma.1.2.1 : Site 2) ∈ rlc_reflectedPrimalRegion K ↔
      ![-(gamma.1.2.1 : Site 2) 0,
        (gamma.1.2.1 : Site 2) 1 - 1] ∈ K := by
  rw [rlc_mem_reflectedPrimalRegion_iff]
  have h : rlc_primalDualReflect.symm (gamma.1.2.1 : Site 2) =
      ![-(gamma.1.2.1 : Site 2) 0, (gamma.1.2.1 : Site 2) 1 - 1] := by
    ext i
    fin_cases i <;> simp
  rw [h]


theorem rlc_left_start_mem_reflectedPrimalRegion_iff {n : ℤ}
    (gamma' : RlcLeftDiagonalPath n) (K : Set (Site 2)) :
    (gamma'.1.1 : Site 2) ∈ rlc_reflectedPrimalRegion K ↔
      ![-(gamma'.1.1 : Site 2) 0,
        (gamma'.1.1 : Site 2) 1 - 1] ∈ K := by
  rw [rlc_mem_reflectedPrimalRegion_iff]
  have h : rlc_primalDualReflect.symm (gamma'.1.1 : Site 2) =
      ![-(gamma'.1.1 : Site 2) 0, (gamma'.1.1 : Site 2) 1 - 1] := by
    ext i
    fin_cases i <;> simp
  rw [h]


theorem rlc_left_end_mem_reflectedPrimalRegion_iff {n : ℤ}
    (gamma' : RlcLeftDiagonalPath n) (K : Set (Site 2)) :
    (gamma'.1.2.1 : Site 2) ∈ rlc_reflectedPrimalRegion K ↔
      ![-(gamma'.1.2.1 : Site 2) 0,
        (gamma'.1.2.1 : Site 2) 1 - 1] ∈ K := by
  rw [rlc_mem_reflectedPrimalRegion_iff]
  have h : rlc_primalDualReflect.symm (gamma'.1.2.1 : Site 2) =
      ![-(gamma'.1.2.1 : Site 2) 0, (gamma'.1.2.1 : Site 2) 1 - 1] := by
    ext i
    fin_cases i <;> simp
  rw [h]



theorem rlc_reflectedEndpointXor_iff_affine_preimages {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (K : Set (Site 2)) :
    RlcReflectedEndpointXor gamma gamma' K ↔
      ((![-(gamma.1.1 : Site 2) 0,
          (gamma.1.1 : Site 2) 1 - 1] ∈ K) ≠
        (![-(gamma.1.2.1 : Site 2) 0,
          (gamma.1.2.1 : Site 2) 1 - 1] ∈ K)) ∧
      ((![-(gamma'.1.1 : Site 2) 0,
          (gamma'.1.1 : Site 2) 1 - 1] ∈ K) ≠
        (![-(gamma'.1.2.1 : Site 2) 0,
          (gamma'.1.2.1 : Site 2) 1 - 1] ∈ K)) := by
  unfold RlcReflectedEndpointXor
  rw [rlc_right_start_mem_reflectedPrimalRegion_iff,
    rlc_right_end_mem_reflectedPrimalRegion_iff,
    rlc_left_start_mem_reflectedPrimalRegion_iff,
    rlc_left_end_mem_reflectedPrimalRegion_iff]




theorem rlc_reflectedEndpointXor_of_affine_preimage_sides {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (K : Set (Site 2))
    (hr0 : ![-(gamma.1.1 : Site 2) 0,
      (gamma.1.1 : Site 2) 1 - 1] ∈ K)
    (hr1 : ![-(gamma.1.2.1 : Site 2) 0,
      (gamma.1.2.1 : Site 2) 1 - 1] ∉ K)
    (hl0 : ![-(gamma'.1.1 : Site 2) 0,
      (gamma'.1.1 : Site 2) 1 - 1] ∉ K)
    (hl1 : ![-(gamma'.1.2.1 : Site 2) 0,
      (gamma'.1.2.1 : Site 2) 1 - 1] ∈ K) :
    RlcReflectedEndpointXor gamma gamma' K := by
  rw [rlc_reflectedEndpointXor_iff_affine_preimages]
  exact ⟨by tauto, by tauto⟩

end Universality
end StatMech

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































import Mathlib
import Code.Ising.DualWalkBoundsClose

open scoped BigOperators
open Finset SimpleGraph

namespace StatMech

namespace Walls

open StatMech.Lattice StatMech.Ising










theorem kwc_crossEdge_symm_eq_map (e : Sym2 (Site 2)) :
    crossEdge.symm e = Sym2.map rot90Inv e := by
  rfl


theorem kwc_rot90Iso_symm_apply (x : Site 2) : rot90Iso.symm x = rot90Inv x := by
  rfl






theorem kwc_mapped_walk_edges {w : Site 2} (W : (hypercubicLattice 2).Walk w w) :
    (W.map rot90Iso.symm.toHom).edges
      = W.edges.map crossEdge.symm := by
  rw [SimpleGraph.Walk.edges_map]
  apply List.map_congr_left
  intro e _
  rw [kwc_crossEdge_symm_eq_map]
  rfl





theorem kwc_pullback_eq_mapped_edges {w : Site 2} (W : (hypercubicLattice 2).Walk w w) :
    (W.edges.toFinset).image crossEdge.symm
      = (W.map rot90Iso.symm.toHom).edges.toFinset := by
  rw [kwc_mapped_walk_edges W]
  ext e
  rw [Finset.mem_image, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, List.mem_toFinset.mp hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, List.mem_toFinset.mpr hg, rfl⟩

















def PrimalWalkBoundsRegion : Prop :=
  ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a), ∃ S : Set (Site 2),
    ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ Vc.edges.toFinset ↔ bdEdge S s(u, v))







theorem kwc_latticeDualWalkHasBdEdgeRegion_of_primal
    (hprimal : PrimalWalkBoundsRegion) :
    LatticeDualWalkHasBdEdgeRegion (hypercubicLattice 2) := by
  intro w W
  obtain ⟨S, hS⟩ := hprimal (W.map rot90Iso.symm.toHom)
  refine ⟨S, ?_⟩
  intro u v huv
  rw [kwc_pullback_eq_mapped_edges W]
  exact hS huv





theorem kwc_dualWalkBoundsRegion_of_primal (hprimal : PrimalWalkBoundsRegion) :
    DualWalkBoundsRegion (hypercubicLattice 2) (hypercubicLattice 2) crossEdge :=
  dualWalkBoundsRegion_lattice_of_bdEdgeMatch
    (kwc_latticeDualWalkHasBdEdgeRegion_of_primal hprimal)















def kwc_PrimalWalkLeftRegionMatch : Prop :=
  ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a),
    ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ Vc.edges.toFinset ↔ bdEdge (jec_leftRegion Vc) s(u, v))





theorem kwc_primalWalkBoundsRegion_of_leftRegionMatch
    (hmatch : kwc_PrimalWalkLeftRegionMatch) :
    PrimalWalkBoundsRegion := by
  intro a Vc
  exact ⟨jec_leftRegion Vc, fun h => hmatch Vc h⟩







theorem kwc_leftRegion_bdEdge_incident {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) {u v : Site 2}
    (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
    u ∈ Vc.support ∨ v ∈ Vc.support :=
  jec_leftRegion_bdEdge_support Vc hadj hbd














theorem kwc_primalWalkBoundsRegion_nil_case {a : Site 2} :
    ∃ S : Set (Site 2), ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk a a).edges.toFinset
        ↔ bdEdge S s(u, v)) := by
  refine ⟨(∅ : Set (Site 2)), ?_⟩
  intro u v _
  simp only [SimpleGraph.Walk.edges_nil, List.toFinset_nil, Finset.notMem_empty, bdEdge_mk,
    Set.mem_empty_iff_false, not_false_iff]
  tauto

end Walls

end StatMech

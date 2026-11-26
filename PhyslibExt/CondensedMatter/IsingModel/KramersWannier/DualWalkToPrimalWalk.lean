/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import PhyslibExt.CondensedMatter.IsingModel.KramersWannier.DualWalkLeftRegion

/-!
# Reducing the dual-walk region property on `ℤ²` to primal walks

The quarter-turn correspondence `crossEdge` maps closed walks of `ℤ²` to closed walks of `ℤ²`, so
the region-boundary property for closed dual walks reduces to the same property for closed primal
walks.

## i. Overview

Under `crossEdge`, the pullback of the edges of a closed lattice walk `W` is the edge set of the
rotated walk `W.map rot90Iso.symm`. The stronger `kwc_PrimalWalkLeftRegionMatch`
(the edge set of every closed walk is the boundary of its own inside region) implies
`PrimalWalkBoundsRegion`. The vacuous reductions from `PrimalWalkBoundsRegion` to the
dual-walk region property were removed.

Headline fidelity: both hypotheses are false.
- `PrimalWalkBoundsRegion` is refuted by `StatMech.Walls.fwr_primalWalkBoundsRegion_false`
  (FaceRegion).
- `kwc_PrimalWalkLeftRegionMatch` is refuted by `StatMech.Walls.ceo_primalWalkLeftRegionMatch_false`
  (ShiftSquareCycle).

The false-to-false helper `kwc_primalWalkBoundsRegion_of_leftRegionMatch` was removed; the
direct refutation is `ceo_primalWalkLeftRegionMatch_false`. The walk lemmas in section A are
unconditional.

## ii. Key results

- `StatMech.Walls.kwc_pullback_eq_mapped_edges` : the `crossEdge` pullback is a rotated walk
- `StatMech.Walls.PrimalWalkBoundsRegion` : the (false) primal region-boundary property
- `StatMech.Walls.kwc_PrimalWalkLeftRegionMatch` : the (false) inside-region matching property

## iii. Table of contents

- A. Rotated walks
- B. Reduction to primal walks

## iv. References

None beyond those in the imported modules.
-/

@[expose] public section

open scoped BigOperators
open Finset SimpleGraph

namespace StatMech

namespace Walls

open StatMech.Lattice StatMech.Ising

/-! ## A. Rotated walks -/

/-- `crossEdge.symm` is the edge map of the inverse quarter turn. -/
lemma kwc_crossEdge_symm_eq_map (e : Sym2 (Site 2)) :
    crossEdge.symm e = Sym2.map rot90Inv e := by
  rfl

/-- The inverse of the quarter-turn isomorphism is `rot90Inv`. -/
lemma kwc_rot90Iso_symm_apply (x : Site 2) : rot90Iso.symm x = rot90Inv x := by
  rfl

/-- The edges of the rotated walk are the `crossEdge.symm` images of the edges of `W`. -/
lemma kwc_mapped_walk_edges {w : Site 2} (W : (hypercubicLattice 2).Walk w w) :
    (W.map rot90Iso.symm.toHom).edges
      = W.edges.map crossEdge.symm := by
  rw [SimpleGraph.Walk.edges_map]
  apply List.map_congr_left
  intro e _
  rw [kwc_crossEdge_symm_eq_map]
  rfl

/-- The `crossEdge` pullback of the edges of `W` is the edge set of the rotated walk. -/
lemma kwc_pullback_eq_mapped_edges {w : Site 2} (W : (hypercubicLattice 2).Walk w w) :
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

/-! ## B. Reduction to primal walks -/

/-- The edge set of every closed walk of `ℤ²` is the boundary-edge set of some set of sites. This is
false (`fwr_primalWalkBoundsRegion_false`). -/
def PrimalWalkBoundsRegion : Prop :=
  ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a), ∃ S : Set (Site 2),
    ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ Vc.edges.toFinset ↔ bdEdge S s(u, v))

/-- The edge set of every closed walk of `ℤ²` is the boundary-edge set of its inside region
`jec_leftRegion`. This is false (`ceo_primalWalkLeftRegionMatch_false`). -/
def kwc_PrimalWalkLeftRegionMatch : Prop :=
  ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a),
    ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ Vc.edges.toFinset ↔ bdEdge (jec_leftRegion Vc) s(u, v))

/-- The trivial closed walk has empty edge set, the boundary of the empty set. -/
lemma kwc_primalWalkBoundsRegion_nil_case {a : Site 2} :
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

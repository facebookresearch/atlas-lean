/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitInteriorOdd

/-!
# The origin is inside the face loop of its cluster

For a site `q` left of a closed walk `Vc`, the ray count of `Vc` at the origin is odd iff a path
from the origin to `q` crosses the boundary of the inside of `Vc` an odd number of times. If the
boundary edges of the origin cluster are exactly those of the inside of the face loop
(`pww_BdEdgeMatch`), crossing counts agree, so the origin, which is in the cluster, has odd ray
count.

## Main definitions

* `StatMech.Lattice.pww_BdEdgeMatch K Vc`: `K` and the inside of `Vc` have the same boundary edges.

## Main results

* `StatMech.Lattice.pww_farLeft_notMem_leftRegion`: sites left of the walk are outside.
* `StatMech.Lattice.pww_crossCount_eq_of_bdEdge_match`: sets with the same boundary edges have the
  same crossing counts.
* `StatMech.Lattice.pww_origin_rayCount_odd`: under `pww_BdEdgeMatch`, the origin has odd ray count.
* `StatMech.Lattice.pww_orbitIsLoop_of_bdEdge_match`: under `pww_BdEdgeMatch` and exterior
  connectivity, the origin cluster is the inside of its face loop.
-/

@[expose] public section

open Set SimpleGraph

namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}

theorem pww_farLeft_notMem_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {q : Site 2} (hq : ∀ p ∈ Vc.support, q 0 ≤ p 0) :
    q ∉ jec_leftRegion Vc := by
  rw [jec_mem_leftRegion, not_not]
  rw [jec_rayCount_eq_zero_of_right q Vc hq]
  exact Nat.even_iff.mpr rfl

theorem pww_oddRay_iff_oddCross_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {q : Site 2} (hq : ∀ p ∈ Vc.support, q 0 ≤ p 0)
    (γ : (hypercubicLattice 2).Walk (origin 2) q) :
    (¬ Even (jec_rayCount (origin 2) Vc)) ↔
      (¬ Even (crossCount (jec_leftRegion Vc) γ)) := by
  have hqout : ¬ ¬ Even (jec_rayCount q Vc) :=
    not_not.mpr (by
      rw [jec_rayCount_eq_zero_of_right q Vc hq]; exact Nat.even_iff.mpr rfl)
  have hpar := crossCount_parity (jec_leftRegion Vc) γ
  simp only [jec_mem_leftRegion] at hpar
  constructor
  · intro hodd heven
    have hside := hpar.mp heven
    exact hqout (hside.mp hodd)
  · intro hcrossOdd hray
    apply hcrossOdd
    rw [hpar]
    constructor
    · intro h; exact absurd h (not_not.mpr hray)
    · intro h; exact absurd h hqout

theorem pww_crossCount_eq_of_bdEdge_match (S T : Set (Site 2))
    (hbd : ∀ e : Sym2 (Site 2), bdEdge S e ↔ bdEdge T e)
    {x y : Site 2} (w : (hypercubicLattice 2).Walk x y) :
    crossCount S w = crossCount T w := by
  classical
  rw [crossCount, crossCount]
  refine List.countP_congr ?_
  intro e _he
  simp only [decide_eq_true_eq]
  exact hbd e

/-- The set `K` and the inside `jec_leftRegion Vc` of the closed walk `Vc` have the same boundary
edges. -/
def pww_BdEdgeMatch (K : Set (Site 2)) {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∀ e : Sym2 (Site 2), bdEdge K e ↔ bdEdge (jec_leftRegion Vc) e

theorem pww_oddRay_of_bdEdge_match (hfin : (cluster 2 ω (origin 2)).Finite) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    (hmatch : pww_BdEdgeMatch (cluster 2 ω (origin 2)) Vc)
    {q : Site 2} (hqK : q ∉ cluster 2 ω (origin 2))
    (hqfar : ∀ p ∈ Vc.support, q 0 ≤ p 0)
    (γ : (hypercubicLattice 2).Walk (origin 2) q) :
    ¬ Even (jec_rayCount (origin 2) Vc) := by
  have hoddK : ¬ Even (crossCount (cluster 2 ω (origin 2)) γ) :=
    orbit_origin_crossCount_odd (ω := ω) hfin hqK γ
  have heq : crossCount (jec_leftRegion Vc) γ = crossCount (cluster 2 ω (origin 2)) γ :=
    pww_crossCount_eq_of_bdEdge_match (jec_leftRegion Vc) (cluster 2 ω (origin 2))
      (fun e => (hmatch e).symm) γ
  have hoddL : ¬ Even (crossCount (jec_leftRegion Vc) γ) := by rw [heq]; exact hoddK
  exact (pww_oddRay_iff_oddCross_leftRegion Vc hqfar γ).mpr hoddL

theorem pww_origin_rayCount_odd (hfin : (cluster 2 ω (origin 2)).Finite) (e : Dart)
    (he : IsBoundaryDart (cluster 2 ω (origin 2)) e)
    (hmatch : pww_BdEdgeMatch (cluster 2 ω (origin 2))
      (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he))
    {q : Site 2} (hqK : q ∉ cluster 2 ω (origin 2))
    (hqfar : ∀ p ∈ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support, q 0 ≤ p 0)
    (γ : (hypercubicLattice 2).Walk (origin 2) q) :
    ¬ Even (jec_rayCount (origin 2)
      (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he)) :=
  pww_oddRay_of_bdEdge_match (ω := ω) hfin _ hmatch hqK hqfar γ

theorem pww_orbitIsLoop_of_bdEdge_match (hfin : (cluster 2 ω (origin 2)).Finite) (e : Dart)
    (he : IsBoundaryDart (cluster 2 ω (origin 2)) e)
    (ho : origin 2 ∈ cluster 2 ω (origin 2))
    (hExt : ∀ z, z ∉ cluster 2 ω (origin 2) → ∃ z0 : Site 2,
      ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support) ∧
      (∀ qq ∈ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support, z0 0 ≤ qq 0))
    (hInt : ∀ z, z ∈ cluster 2 ω (origin 2) →
      ∃ p : (hypercubicLattice 2).Walk z (origin 2),
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support))
    (hmatch : pww_BdEdgeMatch (cluster 2 ω (origin 2))
      (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he))
    {q : Site 2} (hqK : q ∉ cluster 2 ω (origin 2))
    (hqfar : ∀ p ∈ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support, q 0 ≤ p 0)
    (γ : (hypercubicLattice 2).Walk (origin 2) q) :
    ccs_OrbitIsLoop (cluster 2 ω (origin 2)) :=
  ooi_orbitIsLoop_of_witness (cluster 2 ω (origin 2)) hfin e he hExt ho
    (pww_origin_rayCount_odd (ω := ω) hfin e he hmatch hqK hqfar γ) hInt

end Lattice

end StatMech

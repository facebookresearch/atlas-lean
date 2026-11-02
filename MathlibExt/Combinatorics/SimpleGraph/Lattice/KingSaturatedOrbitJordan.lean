/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanClusterBridge
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.MinimalPeriodLoop

/-!
# The boundary orbit of a king-saturated set bounds exactly one region

A cycle `c` in the square lattice `ℤ²` defines a finite plane subgraph (its vertices and edges).
It is connected and has as many edges as vertices, so its cycle rank is one and, by the discrete
Jordan curve theorem, it has exactly one bounded region (finite connected component of the faces
of `ℤ²` not separated by an edge of the cycle).

For a set `K ⊆ ℤ²` and a boundary dart `a`, one period of the `dartNext` orbit of `a` traces a
closed walk `mpl_orbitLoop K a` through the faces along the boundary of `K`. If `K` is
king-saturated (whenever it contains two diagonally opposite corners of a unit square it contains a
third corner), the orbit never visits a face twice, so for period at least three the orbit loop is a
cycle and bounds exactly one region. The unit cell, the domino and the L-tromino are
king-saturated; the diagonal pair `{(0, 0), (1, 1)}` is not
(`StatMech.Lattice.jcb_diagK_not_kingSat`).

## Main definitions

* `StatMech.Lattice.joc_cycleSubgraph c hc`: a lattice cycle as a plane subgraph of `ℤ²`.
* `StatMech.Lattice.joc_Ltromino`: the L-tromino `{(0, 0), (1, 0), (0, 1)}`.

## Main results

* `StatMech.Lattice.joc_cycle_nullity_one`: a lattice cycle has cycle rank one.
* `StatMech.Lattice.joc_cycle_uniqueBoundedRegion`: discrete Jordan curve theorem, a lattice cycle
  has exactly one bounded region.
* `StatMech.Lattice.joc_kingSaturated_orbitLoop_isCycle`: for a king-saturated set, an orbit loop of
  period at least three is a cycle.
* `StatMech.Lattice.joc_kingSaturated_orbit_uniqueBoundedRegion`: such an orbit loop has exactly one
  bounded region.
* `StatMech.Lattice.joc_noLocalPinch_of_kingSaturated`: boundary darts of a king-saturated set
  with the same face point the same way.

## References

* C. Jordan, *Cours d'analyse de l'École polytechnique* (1887).
* C. Thomassen, *The Jordan–Schönflies theorem and the classification of surfaces*,
  Amer. Math. Monthly 99 (1992).
-/

@[expose] public section

open SimpleGraph Set Function

namespace StatMech

namespace Lattice

/-- A cycle `c` of the square lattice as a plane subgraph of `ℤ²`: the vertices and edges of `c`,
embedded by inclusion. -/
noncomputable def joc_cycleSubgraph {v : Site 2} (c : (hypercubicLattice 2).Walk v v)
    (_hc : c.IsCycle) : PlanarZ2Subgraph where
  V := c.toSubgraph.verts
  finV := by
    have h : c.toSubgraph.verts = {w | w ∈ c.support} := SimpleGraph.Walk.verts_toSubgraph c
    rw [h]
    exact (Set.Finite.ofFinset c.support.toFinset (by intro x; simp)).to_subtype
  decV := inferInstance
  G := c.toSubgraph.coe
  emb := ⟨Subtype.val, Subtype.val_injective⟩
  isSub := fun x y hadj => c.toSubgraph.coe_adj_sub x y hadj

/-- The plane subgraph of a lattice cycle is connected. -/
theorem joc_cycleSubgraph_connected {v : Site 2} (c : (hypercubicLattice 2).Walk v v)
    (hc : c.IsCycle) : (joc_cycleSubgraph c hc).G.Connected := by
  change c.toSubgraph.coe.Connected
  have h := c.toSubgraph_connected
  rwa [SimpleGraph.Subgraph.connected_iff'] at h

/-- The plane subgraph of a lattice cycle has as many edges as the cycle has steps. -/
theorem joc_cycle_edge_card {v : Site 2} (c : (hypercubicLattice 2).Walk v v) (hc : c.IsCycle) :
    (joc_cycleSubgraph c hc).G.edgeSet.ncard = c.length := by
  change c.toSubgraph.coe.edgeSet.ncard = c.length
  have hcoe : c.toSubgraph.coe.edgeSet.ncard = c.toSubgraph.edgeSet.ncard := by
    have hinj : Set.InjOn (Sym2.map (Subtype.val : c.toSubgraph.verts → Site 2))
        c.toSubgraph.coe.edgeSet :=
      Set.injOn_of_injective (Sym2.map.injective Subtype.val_injective)
    calc c.toSubgraph.coe.edgeSet.ncard
        = (Sym2.map (Subtype.val) '' c.toSubgraph.coe.edgeSet).ncard := (hinj.ncard_image).symm
      _ = c.toSubgraph.edgeSet.ncard := by rw [SimpleGraph.Subgraph.image_coe_edgeSet_coe]
  rw [hcoe, SimpleGraph.Walk.edgeSet_toSubgraph]
  have hnd : c.edges.Nodup := hc.isCircuit.isTrail.edges_nodup
  have hs : c.edgeSet = ↑c.edges.toFinset := by ext e; simp [SimpleGraph.Walk.mem_edgeSet]
  rw [hs, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, c.length_edges]

/-- The plane subgraph of a lattice cycle has as many vertices as the cycle has steps. -/
theorem joc_cycle_vert_card {v : Site 2} (c : (hypercubicLattice 2).Walk v v) (hc : c.IsCycle) :
    Nat.card (joc_cycleSubgraph c hc).V = c.length := by
  change Nat.card c.toSubgraph.verts = c.length
  rw [Nat.card_coe_set_eq, SimpleGraph.Walk.verts_toSubgraph]
  have hset : {w | w ∈ c.support} = ↑c.support.toFinset := by ext w; simp
  rw [hset, Set.ncard_coe_finset]
  have htailnd : c.support.tail.Nodup := hc.support_nodup
  have hvtail : v ∈ c.support.tail := SimpleGraph.Walk.end_mem_tail_support hc.not_nil
  have hcons : c.support = v :: c.support.tail := (c.cons_tail_support).symm
  have htf : c.support.toFinset = c.support.tail.toFinset := by
    conv_lhs => rw [hcons]
    rw [List.toFinset_cons, Finset.insert_eq_self.mpr (by simp [hvtail])]
  rw [htf, List.toFinset_card_of_nodup htailnd]
  have hlen : c.support.length = c.length + 1 := c.length_support
  rw [hcons] at hlen; simp only [List.length_cons] at hlen; omega

/-- A lattice cycle has cycle rank `|E| + 1 - |V| = 1`. -/
theorem joc_cycle_nullity_one {v : Site 2} (c : (hypercubicLattice 2).Walk v v) (hc : c.IsCycle) :
    nullity (joc_cycleSubgraph c hc).G = 1 := by
  refine jcb_nullity_eq_one_of_connected_card_eq _ (joc_cycleSubgraph_connected c hc) ?_
  rw [joc_cycle_edge_card c hc, joc_cycle_vert_card c hc]

/-- **Discrete Jordan curve theorem** for lattice cycles: a cycle in `ℤ²` has exactly one bounded
region, that is, exactly one finite connected component of the faces of `ℤ²` joined across lattice
edges not on the cycle. The statement counts bounded regions only; that there is a single unbounded
region is a separate fact (compare `StatMech.Lattice.jcs_cycle_faceCount_eq_two`). Reference:
C. Jordan, *Cours d'analyse* (1887); discrete form in C. Thomassen, *The Jordan–Schönflies theorem
and the classification of surfaces* (1992). -/
theorem joc_cycle_uniqueBoundedRegion {v : Site 2} (c : (hypercubicLattice 2).Walk v v)
    (hc : c.IsCycle) : Nat.card (jcb_BoundedRegion (joc_cycleSubgraph c hc)) = 1 :=
  jcb_boundedRegion_card_eq_one_of_nullity_one _ (joc_cycle_nullity_one c hc)

/-- If one period of the boundary orbit of `a` has length at least three and visits each face at
most once, the orbit loop is a cycle with exactly one bounded region. -/
theorem joc_orbitLoop_uniqueBoundedRegion (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a))) :
    Nat.card (jcb_BoundedRegion (joc_cycleSubgraph (mpl_orbitLoop K a)
      (mpl_orbitLoop_isCycle K a hp hinj))) = 1 :=
  joc_cycle_uniqueBoundedRegion _ (mpl_orbitLoop_isCycle K a hp hinj)

/-- For a king-saturated set `K`, the orbit loop of a boundary dart with period at least three is a
cycle. -/
theorem joc_kingSaturated_orbitLoop_isCycle (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hp : 3 ≤ dartOrbitPeriod K a)
    (hks : npm_KingSaturated K) : (mpl_orbitLoop K a).IsCycle :=
  mpl_orbitLoop_isCycle K a hp (npm_orbitFace_injOn K a hks)

/-- For a king-saturated set `K`, the orbit loop of a boundary dart with period at least three has
exactly one bounded region. -/
theorem joc_kingSaturated_orbit_uniqueBoundedRegion (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hp : 3 ≤ dartOrbitPeriod K a)
    (hks : npm_KingSaturated K) :
    Nat.card (jcb_BoundedRegion (joc_cycleSubgraph (mpl_orbitLoop K a)
      (joc_kingSaturated_orbitLoop_isCycle K a hp hks))) = 1 :=
  joc_cycle_uniqueBoundedRegion _ (joc_kingSaturated_orbitLoop_isCycle K a hp hks)

/-- The one-site set `{(0, 0)}` is king-saturated. -/
theorem joc_unitCell_kingSaturated : npm_KingSaturated unitCell := by
  intro f
  simp only [unitCell, npd_P00, npd_P11, npd_P10, npd_P01, Set.mem_singleton_iff, site2_eq]
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩ <;> omega

/-- The boundary orbit of the one-site set (period four) is a cycle with exactly one bounded
region. -/
theorem joc_unitCell_orbit_uniqueBoundedRegion :
    Nat.card (jcb_BoundedRegion (joc_cycleSubgraph (mpl_orbitLoop unitCell ucBase)
      (joc_kingSaturated_orbitLoop_isCycle unitCell ucBase
        (by rw [unitCell_orbitPeriod_eq_four]; norm_num) joc_unitCell_kingSaturated))) = 1 :=
  joc_kingSaturated_orbit_uniqueBoundedRegion unitCell ucBase
    (by rw [unitCell_orbitPeriod_eq_four]; norm_num) joc_unitCell_kingSaturated

/-- The domino `{(0, 0), (1, 0)}` is king-saturated. -/
theorem joc_domino_kingSaturated : npm_KingSaturated domino := by
  intro f
  simp only [domino, npd_P00, npd_P11, npd_P10, npd_P01, Set.mem_insert_iff,
    Set.mem_singleton_iff, site2_eq]
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩ <;>
    (rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> omega)

/-- The boundary orbit of the domino (period six) is a cycle with exactly one bounded region. -/
theorem joc_domino_orbit_uniqueBoundedRegion :
    Nat.card (jcb_BoundedRegion (joc_cycleSubgraph (mpl_orbitLoop domino dmBase)
      (joc_kingSaturated_orbitLoop_isCycle domino dmBase
        (by rw [domino_orbitPeriod_eq_six]; norm_num) joc_domino_kingSaturated))) = 1 :=
  joc_kingSaturated_orbit_uniqueBoundedRegion domino dmBase
    (by rw [domino_orbitPeriod_eq_six]; norm_num) joc_domino_kingSaturated

/-- The L-tromino `{(0, 0), (1, 0), (0, 1)}`. -/
def joc_Ltromino : Set (Site 2) := {![0, 0], ![1, 0], ![0, 1]}

/-- The L-tromino is king-saturated. -/
theorem joc_Ltromino_kingSaturated : npm_KingSaturated joc_Ltromino := by
  intro f
  simp only [joc_Ltromino, npd_P00, npd_P11, npd_P10, npd_P01, Set.mem_insert_iff,
    Set.mem_singleton_iff, site2_eq]
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩ <;>
    (rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> omega)

/-- The boundary orbit of the L-tromino visits every face at most once per period. -/
theorem joc_Ltromino_faceMultiplicityOne
    (a : {e : Dart // IsBoundaryDart joc_Ltromino e}) :
    usc_FaceMultiplicityOne joc_Ltromino a :=
  emb_faceMultiplicityOne_of_kingSaturated joc_Ltromino a joc_Ltromino_kingSaturated

/-- Two boundary darts of a king-saturated set with the same face point in the same direction:
king-saturated sets have no diagonal pinch. -/
theorem joc_noLocalPinch_of_kingSaturated {K : Set (Site 2)} (hks : npm_KingSaturated K)
    {e₁ e₂ : Dart} (he₁ : IsBoundaryDart K e₁) (he₂ : IsBoundaryDart K e₂)
    (hface : dartFace e₁ = dartFace e₂) : e₁.dir = e₂.dir := by
  have hnt : npd_NoDiagTouch K := npm_noDiagTouch_of_kingSaturated hks
  exact npd_noPinch_local_of_noDiagTouch he₁ he₂ hface (hnt (dartFace e₁))

end Lattice

end StatMech

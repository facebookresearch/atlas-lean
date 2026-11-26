/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.PcUpperEnclosure
public import MathlibExt.Probability.Percolation.Universality.DualCircuitToWalk

/-!
# Face-boundary cycles around the left-reach set

Faces of `ℤ²` are indexed by their lower-left corners, and two adjacent faces `f, g` are separated
by the primal edge `sharedPrimalEdge f g`. The face-boundary graph `faceBoundaryGraph S` joins
adjacent faces whose separating edge has exactly one endpoint in `S`; for a finite `S` with
nonempty edge boundary it contains a cycle (`exists_dualCircuit_of_finite_of_edgeBoundary`).

This file applies that to the left-reach set `bcd_leftReach ω n` of `rect 0 n 0 n`: without an
open horizontal crossing, the face-boundary graph of the left-reach set has a cycle. This is a step
towards the box-crossing dichotomy but not the dichotomy itself. The cycle surrounds the whole
left-reach set, so some of its dual edges cross edges leaving the square, which need not be closed;
the cycle is neither shown to be closed in `ω` nor to run from the bottom to the top of the square.

It also records the bookkeeping between the face picture and the rotated dual `dualConfig ω`:
`crossEdge (sharedPrimalEdge f g)` is open in `dualConfig ω` exactly when the separating edge is
closed, but `crossEdge (sharedPrimalEdge f g)` is not the face edge `s(f, g)`
(`fdd_straight_dualEdges_disjoint`).

## Main results

* `StatMech.Universality.fdd_cluster_dualCircuit_open`: a finite open cluster is surrounded by a
  face-boundary cycle all of whose separating edges are closed.
* `StatMech.Universality.fdd_leftReach_dualCircuit`: without a horizontal crossing the left-reach
  set has a face-boundary cycle.
* `StatMech.Universality.fdd_square_dichotomy`: the bundle of these facts for the square.
-/

@[expose] public section

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}

/-- The quarter turn of the edge separating two adjacent faces is a lattice edge between quarter
turns of sites. -/
theorem fdd_faceBoundary_dualEdge_isLatticeEdge {f g : Site 2}
    (h : (hypercubicLattice 2).Adj f g) :
    ∃ p q : Site 2, crossEdge (sharedPrimalEdge f g) = s(rot90Fun p, rot90Fun q) ∧
      (hypercubicLattice 2).Adj (rot90Fun p) (rot90Fun q) := by
  obtain ⟨p, q, hpq, hadj⟩ := sharedPrimalEdge_isLatticeEdge h
  exact ⟨p, q, by rw [hpq, crossEdge_mk], (rot90_adj p q).mpr hadj⟩

/-- A closed lattice edge `{p, q}` gives the edge `{rot90Fun p, rot90Fun q}` of the
`dualConfig ω`-open graph. -/
theorem fdd_faceBoundaryGraph_dualAdj (ω : ConfigSpace (Sym2 (Site 2))) {p q : Site 2}
    (hadj : (hypercubicLattice 2).Adj p q) (hclosed : ω s(p, q) = false) :
    (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun p) (rot90Fun q) := by
  refine ⟨(rot90_adj p q).mpr hadj, ?_⟩
  have : dualConfig ω (crossEdge s(p, q)) = true := by
    rw [StatMech.RSW.dualCross_open_iff_closed]; exact hclosed
  rwa [crossEdge_mk] at this

/-- Every face-boundary edge of an open cluster separates the faces by a closed edge, so the
quarter turn of that edge is open in `dualConfig ω`. The closedness is
`StatMech.Percolation.sharedPrimalEdge_isClosed`. -/
theorem fdd_cluster_faceBoundary_edge_dual_open (o : Site 2) {f g : Site 2}
    (h : (faceBoundaryGraph (cluster 2 ω o)).Adj f g) :
    dualConfig ω (crossEdge (sharedPrimalEdge f g)) = true :=
  (StatMech.RSW.dualCross_open_iff_closed ω _).mpr (Percolation.sharedPrimalEdge_isClosed o h)

/-- A finite open cluster is surrounded by a face-boundary cycle whose separating edges are all
closed (stated through `dualConfig ω`). -/
theorem fdd_cluster_dualCircuit_open (o : Site 2) (hfin : (cluster 2 ω o).Finite)
    {z : Site 2} (w : (hypercubicLattice 2).Walk o z) (hz : z ∉ cluster 2 ω o) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω o)).Walk u u),
      c.IsCycle ∧
      (∀ {f g : Site 2}, s(f, g) ∈ c.edges →
        dualConfig ω (crossEdge (sharedPrimalEdge f g)) = true) := by
  obtain ⟨⟨u, c, hcyc⟩, _hsep⟩ := cluster_enclosed_by_dualCircuit o hfin w hz
  refine ⟨u, c, hcyc, ?_⟩
  intro f g hfg
  exact fdd_cluster_faceBoundary_edge_dual_open o (c.adj_of_mem_edges hfg)

/-- The quarter turn of an in-square edge leaving the left-reach set is an edge of the
`dualConfig ω`-open graph. Same as `dcw_barrier_dualAdj`, with the barrier-edge predicate
unpacked. -/
theorem fdd_leftReach_barrierEdge_dualAdj (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {v w : Site 2} (hv : v ∈ bcd_leftReach ω n) (hwbox : w ∈ rect 0 n 0 n)
    (hadj : (hypercubicLattice 2).Adj v w) (hw : w ∉ bcd_leftReach ω n) :
    (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun v) (rot90Fun w) :=
  fdd_faceBoundaryGraph_dualAdj ω hadj (bcd_leftReach_boundary_closed ω n hv hwbox hadj hw)

/-- An edge from the left-reach set to its complement gives an edge of its face-boundary
graph. -/
theorem fdd_leftReach_faceBoundary_adj (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {v w : Site 2} (hv : v ∈ bcd_leftReach ω n) (hw : w ∉ bcd_leftReach ω n)
    (hadj : (hypercubicLattice 2).Adj v w) :
    ∃ f g : Site 2, (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g :=
  exists_faceBoundaryGraph_adj_of_edgeBoundary (bcd_leftReach ω n) (x := v) (y := w)
    ⟨hadj, iff_of_true hv hw⟩

/-- Without a horizontal crossing (`n ≥ 0`), the face-boundary graph of the left-reach set has an
edge. -/
theorem fdd_leftReach_faceBoundary_nonempty (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ f g : Site 2, (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g := by
  obtain ⟨v, w, hbar, _, _⟩ := dcw_barrierEdge_exists ω n hn hnoH
  exact fdd_leftReach_faceBoundary_adj ω n hbar.1 hbar.2.2.1 hbar.2.2.2

/-- Without a horizontal crossing (`n ≥ 0`), the face-boundary graph of the left-reach set
contains a cycle. The cycle need not be closed in `ω` nor span the square; see the module
docstring. -/
theorem fdd_leftReach_dualCircuit (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), c.IsCycle := by
  classical
  obtain ⟨v, w, hbar, _, _⟩ := dcw_barrierEdge_exists ω n hn hnoH
  have hxy : (v, w) ∈ edgeBoundary 2 (bcd_leftReach ω n) :=
    ⟨hbar.2.2.2, iff_of_true hbar.1 hbar.2.2.1⟩
  exact exists_dualCircuit_of_finite_of_edgeBoundary (bcd_leftReach ω n)
    (bcd_leftReach_finite ω n) hxy

theorem fdd_dualEdge_leftSide (a b : ℤ) :
    crossEdge (sharedPrimalEdge ![a, b] ![a - 1, b]) = s(![-b, a], ![-(b + 1), a]) := by
  rw [sharedPrimalEdge_left, crossEdge_mk]; unfold faceCorner00 faceCorner01
  rw [rot90Fun_apply, rot90Fun_apply]

theorem fdd_dualEdge_rightSide (a b : ℤ) :
    crossEdge (sharedPrimalEdge ![a, b] ![a + 1, b]) = s(![-b, a + 1], ![-(b + 1), a + 1]) := by
  rw [sharedPrimalEdge_right, crossEdge_mk]; unfold faceCorner10 faceCorner11
  rw [rot90Fun_apply, rot90Fun_apply]

/-- The quarter turns of the edges separating face `(a, b)` from its left and right neighbors
share no vertex. Hence the quarter-turned separating edges of a face path are not a walk: the
rotated dual `dualConfig` cannot be read in face coordinates. -/
theorem fdd_straight_dualEdges_disjoint (a b : ℤ) {p : Site 2}
    (hp1 : p ∈ crossEdge (sharedPrimalEdge ![a, b] ![a - 1, b]))
    (hp2 : p ∈ crossEdge (sharedPrimalEdge ![a, b] ![a + 1, b])) : False := by
  rw [fdd_dualEdge_leftSide] at hp1
  rw [fdd_dualEdge_rightSide] at hp2
  have h1 : p 1 = a := by
    rw [Sym2.mem_iff] at hp1; rcases hp1 with rfl | rfl <;> simp
  have h2 : p 1 = a + 1 := by
    rw [Sym2.mem_iff] at hp2; rcases hp2 with rfl | rfl <;> simp
  omega

/-- Without a horizontal crossing of `rect 0 n 0 n` (`n ≥ 0`): the left-reach set is finite,
every in-square edge leaving it has an open quarter turn in `dualConfig ω`, and its face-boundary
graph is nonempty and contains a cycle.

Despite the name this is not the box-crossing dichotomy (Grimmett, *Percolation*, 2nd ed., 1999,
Ch. 11; Bollobás–Riordan, *Percolation*, 2006, Ch. 3): no closed dual crossing of the square is
produced, and the cycle is not shown to be closed in `ω`. -/
theorem fdd_square_dichotomy (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    (bcd_leftReach ω n).Finite ∧
      (∀ {v w : Site 2}, v ∈ bcd_leftReach ω n → w ∈ rect 0 n 0 n →
        (hypercubicLattice 2).Adj v w → w ∉ bcd_leftReach ω n →
        (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun v) (rot90Fun w)) ∧
      (∃ f g : Site 2, (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g) ∧
      (∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), c.IsCycle) :=
  ⟨bcd_leftReach_finite ω n,
   fun hv hwbox hadj hw => fdd_leftReach_barrierEdge_dualAdj ω n hv hwbox hadj hw,
   fdd_leftReach_faceBoundary_nonempty ω n hn hnoH,
   fdd_leftReach_dualCircuit ω n hn hnoH⟩

end Universality

end StatMech

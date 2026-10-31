/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.HalfPlaneFiniteStripArms
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.DualTransverse
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.HalfPlaneBarrier

/-!
# A primal strip crossing blocks a transverse dual connection

An open primal path that joins the two sides of a finite vertical strip separates the dual
sources on its left from the dual sources on its right inside a horizontal band.

## i. Overview

`walkArc_coord_strict_bounds_of_support` is a geometric bound: if every vertex of a walk has its
`i`-th coordinate in `(c + B, d - B)` and every edge arc moves at most `B` from its endpoint,
then the whole drawn walk stays strictly inside `(c, d)`.

`finiteStripPrimal_dualPairConnection_disjoint` is the planar duality step. Suppose the primal
configuration `ω` lies in the finite-strip joined boundary-arm event (an open primal arm running
from the left boundary to the right boundary of the strip of width `np` placed at `r`, within the
horizontal band between heights `s` and `s + gap`), and the dual configuration has a dual path
joining dual sources `Ld` to the left of the strip with dual sources `Rd` to its right through
the buffered dual ball, which lies in the middle third of the band. Then the drawn dual path
would cross the drawn primal arm, which planarity forbids, so the two events are disjoint.

Headline fidelity: both results are unconditional (deterministic statements about one
configuration, under the stated edge-arc bounds and positions).

## ii. Key results

- `PeriodicPlaneEmbedding.walkArc_coord_strict_bounds_of_support`
- `PeriodicPlanarDualPair.finiteStripPrimal_dualPairConnection_disjoint`

## iii. Table of contents

- A. Drawn walks inside a coordinate band
- B. Primal strip arms against dual connections

## iv. References

- S. Sheffield, *Random Surfaces*, Astérisque 304 (2005), Ch. 9.
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Ch. 6 (planar duality).
-/

@[expose] public section

open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC StatMech.Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

/-! ## A. Drawn walks inside a coordinate band -/

omit [Countable V] in
/-- If every vertex of the walk `p` has `i`-th coordinate in `(c + B, d - B)` and every edge arc
stays within distance `B` of its starting vertex, then every point of the drawn walk has `i`-th
coordinate in `(c, d)`. -/
lemma PeriodicPlaneEmbedding.walkArc_coord_strict_bounds_of_support
    (E : PeriodicPlaneEmbedding P) {B c d : Real} (hB0 : 0 ≤ B)
    (hB : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc huv t - E.vertex u) i| ≤ B)
    (i : Fin 2) {x y : V} (p : P.graph.Walk x y)
    (hp : ∀ v ∈ p.support,
      c + B < E.vertexCoord v i ∧ E.vertexCoord v i < d - B) :
    ∀ t : unitInterval,
      c < E.coordinates (E.walkArc p t) i ∧
        E.coordinates (E.walkArc p t) i < d := by
  intro t
  have hq : E.walkArc p t ∈ Set.range (E.walkArc p) := ⟨t, rfl⟩
  rcases E.mem_walkArc_range_cases p hq with hstart | hedge
  · have hx := hp x (by simp)
    change E.walkArc p t = E.vertex x at hstart
    rw [hstart]
    change c < E.vertexCoord x i ∧ E.vertexCoord x i < d
    constructor <;> linarith
  · obtain ⟨u, v, huv, hedge, q, hq⟩ := hedge
    have hu := hp u (p.fst_mem_support_of_mem_edges hedge)
    have hlo := E.vertex_sub_le_edgeArc_coord hB huv q i
    have hhi := E.edgeArc_coord_le_vertex_add hB huv q i
    change E.edgeArc huv q = E.walkArc p t at hq
    rw [← hq]
    constructor <;> linarith

/-! ## B. Primal strip arms against dual connections -/

namespace PeriodicPlanarDualPair

/-- Planar blocking: a primal configuration in the finite-strip joined boundary-arm event and a dual
configuration joining the dual sources `Ld` (left of the strip) to `Rd` (right of the strip) within
a buffered dual ball inside the band cannot occur together. -/
lemma finiteStripPrimal_dualPairConnection_disjoint
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V))
    {Bp Bd r s : Real} {gap : Int} {np N : Nat}
    {Lp Rp : Finset V} {Ld Rd : Finset W}
    (hBp0 : 0 ≤ Bp) (hBd0 : 0 ≤ Bd)
    (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ Bp)
    (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ Bd)
    (hgap : 0 < (gap : Real))
    (hLpDeep : (Lp : Set V) ⊆
      D.primalEmbedding.rightHalfPlaneVertices (r + Bp))
    (hLd : ∀ y ∈ Ld,
      D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0 <
        r - Bp - 1)
    (hRd : ∀ y ∈ Rd,
      r + np + Bp + 1 <
        D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0)
    (hbox : ∀ v ∈ Pdual.orbitBox (Pdual.bufferedRadius N),
      (2 * s + (s + gap)) / 3 + Bd <
          D.dualEmbedding.vertexCoord v 1 ∧
        D.dualEmbedding.vertexCoord v 1 <
          (s + 2 * (s + gap)) / 3 - Bd)
    (hprimal : omega ∈
      D.primalEmbedding.finiteStripJoinedBoundaryArmEvent
        r s (s + gap) np Lp Rp)
    (hdual : dualConfigEquiv D.edgeDual omega ∈
      Pdual.finiteInfinitePairConnectionEvent Ld Rd N) : False := by
  have hsgap : s < s + (gap : Real) := by linarith
  have hpgeom :=
    D.primalEmbedding.finiteStripJoinedBoundaryArmEvent_barrierGeometry
      hBp hBp0 hsgap hLpDeep hprimal
  dsimp only at hpgeom
  obtain ⟨hab, hCD, xl, xu, xj, lower, upper,
    hlowerNil, hupperNil, hlowerOpen, hupperOpen,
    hlowerBottom, hupperTop, hlowerX, hupperX⟩ := hpgeom
  obtain ⟨yl, hyl, yr, hyr, dual, hdualSupport, hdualOpen⟩ :=
    Pdual.finiteInfinitePairConnectionEvent_graphWalk hdual
  have hdualLeft := hLd yl hyl
  have hdualRight := hRd yr hyr
  have hylr : yl ≠ yr := by
    intro heq
    subst yr
    linarith
  have hdualNil : ¬ dual.Nil := SimpleGraph.Walk.not_nil_of_ne hylr
  have hdualY' : ∀ t : unitInterval,
      (2 * s + (s + (gap : Real))) / 3 <
          D.dualEmbedding.coordinates (D.dualEmbedding.walkArc dual t) 1 ∧
        D.dualEmbedding.coordinates (D.dualEmbedding.walkArc dual t) 1 <
          (s + 2 * (s + (gap : Real))) / 3 := by
    apply D.dualEmbedding.walkArc_coord_strict_bounds_of_support
      hBd0 hBd (1 : Fin 2) dual
    intro v hv
    exact hbox v (hdualSupport v hv)
  have hdualY : ∀ t : unitInterval,
      (2 * s + (s + (gap : Real))) / 3 <
          D.primalEmbedding.coordinates (D.dualEmbedding.walkArc dual t) 1 ∧
        D.primalEmbedding.coordinates (D.dualEmbedding.walkArc dual t) 1 <
          (s + 2 * (s + (gap : Real))) / 3 := by
    intro t
    simpa only [D.coordinates_eq] using hdualY' t
  exact D.no_open_dual_transverse_walk_of_joined_primal_arms
    omega hab hCD lower upper dual hlowerNil hupperNil hdualNil
    hlowerOpen hupperOpen hdualOpen hdualLeft hdualRight
    hlowerBottom hupperTop hlowerX hupperX hdualY

end PeriodicPlanarDualPair

end StatMech.FK.PeriodicPlanar

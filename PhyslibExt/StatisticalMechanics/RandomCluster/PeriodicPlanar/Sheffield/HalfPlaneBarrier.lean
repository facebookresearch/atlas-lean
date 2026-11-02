/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.Basic

/-!
# Joined primal arms block transverse dual walks

Two open primal arms that meet and stay inside a vertical strip separate the strip, so no open
dual walk can cross the strip horizontally between them.

## i. Overview

Planar duality forbids an open primal edge and an open dual edge from crossing. This file turns
that into a barrier statement. In the continuum, a path that enters a vertical strip
`a < x < b` from the left, leaves it on the right and stays at heights `c < y < d` must meet any
pair of paths that stay in the strip, start below height `c` and above height `d`, and end at a
common point. Applied to the arcs of an open primal pair of walks and an open dual walk, this
gives a contradiction.

Headline fidelity: both results are proved unconditionally (no probabilistic or geometric
hypotheses beyond the displayed coordinate bounds).

## ii. Key results

- `ContinuousHalfPlaneBarrier.joined_boundary_arms_intersect_transverse_path` : the continuum
  barrier.
- `PeriodicPlanarDualPair.no_open_dual_transverse_walk_of_joined_primal_arms` : no open dual
  walk crosses a strip spanned by two joined open primal arms.

## iii. Table of contents

- A. The continuum barrier
- B. The primal–dual barrier

## iv. References

- S. Sheffield, *Random Surfaces*, Astérisque 304 (2005), Ch. 9.
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), §6.1 (planar duality).
-/

@[expose] public section

open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC StatMech.Lattice

/-! ## A. The continuum barrier -/

namespace ContinuousHalfPlaneBarrier

/-- Continuum barrier: two paths in the open strip `a < x < b`, one starting below height `c`,
one above height `d`, and ending at a common point, meet every path that runs from left of
`a` to right of `b` at heights in `(c, d)`. -/
lemma joined_boundary_arms_intersect_transverse_path
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {lo hi j gl gr : Fin 2 → ℝ}
    (lower : Path lo j) (upper : Path hi j) (gamma : Path gl gr)
    (hgl : gl 0 < a) (hgr : b < gr 0)
    (hlo : lo 1 < c) (hhi : d < hi 1)
    (hlowerX : ∀ t : unitInterval, a < lower t 0 ∧ lower t 0 < b)
    (hupperX : ∀ t : unitInterval, a < upper t 0 ∧ upper t 0 < b)
    (hgammaY : ∀ t : unitInterval, c < gamma t 1 ∧ gamma t 1 < d) :
    (Set.range gamma ∩ (Set.range lower ∪ Set.range upper)).Nonempty := by
  let eta := lower.trans upper.symm
  have hetaX : ∀ t : unitInterval, a < eta t 0 ∧ eta t 0 < b := by
    intro t
    have ht : eta t ∈ Set.range eta := ⟨t, rfl⟩
    dsimp only [eta] at ht
    rw [Path.trans_range, Path.symm_range] at ht
    rcases ht with ht | ht
    · obtain ⟨s, hs⟩ := ht
      simpa [hs] using hlowerX s
    · obtain ⟨s, hs⟩ := ht
      simpa [hs] using hupperX s
  obtain ⟨t, s, hcross⟩ :=
    ContinuousRectangleCrossing.strip_paths_intersect hab hcd gamma eta
      hgl hgr hlo hhi hgammaY hetaX
  refine ⟨gamma t, ⟨t, rfl⟩, ?_⟩
  have hs : eta s ∈ Set.range eta := ⟨s, rfl⟩
  dsimp only [eta] at hs
  rw [Path.trans_range, Path.symm_range] at hs
  rw [hcross]
  exact hs

end ContinuousHalfPlaneBarrier

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

/-! ## B. The primal–dual barrier -/

namespace PeriodicPlanarDualPair

/-- Two nontrivial open primal walks ending at a common vertex, with arcs in the strip `a < x <
b`, one starting below `c` and the other above `d`, leave no nontrivial open dual walk
crossing the strip from left of `a` to right of `b` at heights in `(c, d)`. -/
theorem no_open_dual_transverse_walk_of_joined_primal_arms
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V))
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {xl xu xj : V} {yl yr : W}
    (lower : P.graph.Walk xl xj) (upper : P.graph.Walk xu xj)
    (dual : Pdual.graph.Walk yl yr)
    (hlowerNil : ¬ lower.Nil) (hupperNil : ¬ upper.Nil)
    (hdualNil : ¬ dual.Nil)
    (hlowerOpen : ∀ {x y : V}, s(x, y) ∈ lower.edges →
      omega s(x, y) = true)
    (hupperOpen : ∀ {x y : V}, s(x, y) ∈ upper.edges →
      omega s(x, y) = true)
    (hdualOpen : ∀ {x y : W}, s(x, y) ∈ dual.edges →
      dualConfigEquiv D.edgeDual omega s(x, y) = true)
    (hdualLeft : D.primalEmbedding.coordinates
      (D.dualEmbedding.vertex yl) 0 < a)
    (hdualRight : b < D.primalEmbedding.coordinates
      (D.dualEmbedding.vertex yr) 0)
    (hlowerBottom : D.primalEmbedding.vertexCoord xl 1 < c)
    (hupperTop : d < D.primalEmbedding.vertexCoord xu 1)
    (hlowerX : ∀ t : unitInterval,
      a < D.primalEmbedding.coordinates
          (D.primalEmbedding.walkArc lower t) 0 ∧
        D.primalEmbedding.coordinates
          (D.primalEmbedding.walkArc lower t) 0 < b)
    (hupperX : ∀ t : unitInterval,
      a < D.primalEmbedding.coordinates
          (D.primalEmbedding.walkArc upper t) 0 ∧
        D.primalEmbedding.coordinates
          (D.primalEmbedding.walkArc upper t) 0 < b)
    (hdualY : ∀ t : unitInterval,
      c < D.primalEmbedding.coordinates
          (D.dualEmbedding.walkArc dual t) 1 ∧
        D.primalEmbedding.coordinates
          (D.dualEmbedding.walkArc dual t) 1 < d) : False := by
  let lowerC := (D.primalEmbedding.walkArc lower).map
    D.primalEmbedding.coordinates.continuous
  let upperC := (D.primalEmbedding.walkArc upper).map
    D.primalEmbedding.coordinates.continuous
  let dualC := (D.dualEmbedding.walkArc dual).map
    D.primalEmbedding.coordinates.continuous
  have hbarrier :=
    ContinuousHalfPlaneBarrier.joined_boundary_arms_intersect_transverse_path
      hab hcd lowerC upperC dualC hdualLeft hdualRight
      hlowerBottom hupperTop hlowerX hupperX hdualY
  obtain ⟨z, hzdual, hzarms⟩ := hbarrier
  obtain ⟨t, rfl⟩ := hzdual
  rcases hzarms with hzlower | hzupper
  · obtain ⟨s, hs⟩ := hzlower
    have hcross : D.primalEmbedding.walkArc lower s =
        D.dualEmbedding.walkArc dual t := by
      apply D.primalEmbedding.coordinates.injective
      simpa [lowerC, dualC] using hs
    have hdisj := D.no_open_primal_dual_walkArc_crossing omega lower dual
      hlowerNil hdualNil hlowerOpen hdualOpen
    exact Set.disjoint_left.mp hdisj ⟨s, rfl⟩ ⟨t, hcross.symm⟩
  · obtain ⟨s, hs⟩ := hzupper
    have hcross : D.primalEmbedding.walkArc upper s =
        D.dualEmbedding.walkArc dual t := by
      apply D.primalEmbedding.coordinates.injective
      simpa [upperC, dualC] using hs
    have hdisj := D.no_open_primal_dual_walkArc_crossing omega upper dual
      hupperNil hdualNil hupperOpen hdualOpen
    exact Set.disjoint_left.mp hdisj ⟨s, rfl⟩ ⟨t, hcross.symm⟩

end PeriodicPlanarDualPair

end StatMech.FK.PeriodicPlanar

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.PeriodicPlanarSheffield

open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

namespace ContinuousHalfPlaneBarrier




theorem joined_boundary_arms_intersect_transverse_path
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

namespace PeriodicPlanarDualPair





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

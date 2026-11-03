/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.HalfPlaneJoinedArmsHighProbability
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.HalfPlaneBarrier

/-!
# Primal barriers exclude complementary dual crossings

Almost surely there are joined open primal arms in some vertical strip, and such arms rule out
open dual walks crossing every rectangle horizontally.

## i. Overview

`PeriodicPlaneEmbedding.primalHalfPlaneBarrierReady` (defined in
`HalfPlaneJoinedArmsHighProbability`) says that two nontrivial open primal walks meet at a common
vertex, have arcs inside a vertical strip `a < x < b`, and start below height `C` and above
height `D`. Despite its name it does not refer to a half-plane. Under an FKG, translation
invariant measure with an almost surely unique infinite cluster, this event has probability one.
`HasOpenComplementaryDualTransverseWalks` asks for an open dual walk crossing every rectangle
`(a, b) × (c, d)` from left to right; the barrier makes the two events incompatible.

Headline fidelity:
- `primalHalfPlaneBarrierReady_measureReal_eq_one` is conditional on FKG, translation invariance
  and almost sure uniqueness of the infinite cluster.
- `not_primalBarrierReady_and_complementaryDualTransverseWalks` is unconditional.

## ii. Key results

- `PeriodicPlaneEmbedding.primalHalfPlaneBarrierReady_measureReal_eq_one`
- `PeriodicPlanarDualPair.not_primalBarrierReady_and_complementaryDualTransverseWalks`

## iii. Table of contents

- A. Joined primal arms occur almost surely
- B. Exclusion of complementary dual crossings

## iv. References

- S. Sheffield, *Random Surfaces*, Astérisque 304 (2005), Ch. 9.
-/

@[expose] public section

open MeasureTheory Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

/-! ## A. Joined primal arms occur almost surely -/

/-- Under an FKG, translation-invariant probability measure with an almost surely unique infinite
cluster, joined open primal arms in some vertical strip exist almost surely. -/
theorem PeriodicPlaneEmbedding.primalHalfPlaneBarrierReady_measureReal_eq_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
    mu.real E.primalHalfPlaneBarrierReady = 1 := by
  obtain ⟨B, hB0, hB⟩ := E.exists_edgeArc_displacement_bound
  apply le_antisymm measureReal_le_one
  by_contra hnot
  have hlt : mu.real E.primalHalfPlaneBarrierReady < 1 := lt_of_not_ge hnot
  let epsilon : Real := (1 - mu.real E.primalHalfPlaneBarrierReady) / 2
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    linarith
  obtain ⟨L, U, n, hprob, hsub⟩ :=
    E.exists_highProbability_primalHalfPlaneBarrierReady
      mu hFKG hTI hunique 0 B hB0 hB hepsilon
  have hmono : mu.real (E.finiteJoinedBoundaryArmEvent 0 0 1 n L U) ≤
      mu.real E.primalHalfPlaneBarrierReady := measureReal_mono hsub
  dsimp only [epsilon] at hprob
  linarith

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}

/-! ## B. Exclusion of complementary dual crossings -/

namespace PeriodicPlanarDualPair

/-- The configuration has a nontrivial open dual walk starting left of `a`, ending right of `b`,
whose arc stays at heights in `(c, d)` (heights measured in the primal coordinates). -/
def HasOpenComplementaryDualTransverseWalkAt
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V)) (a b c d : Real) : Prop :=
  ∃ yl yr : W, ∃ dual : Pdual.graph.Walk yl yr,
    ¬dual.Nil ∧
      (∀ {x y : W}, s(x, y) ∈ dual.edges →
        dualConfigEquiv D.edgeDual omega s(x, y) = true) ∧
      D.primalEmbedding.coordinates (D.dualEmbedding.vertex yl) 0 < a ∧
      b < D.primalEmbedding.coordinates (D.dualEmbedding.vertex yr) 0 ∧
      ∀ t : unitInterval,
        c < D.primalEmbedding.coordinates
            (D.dualEmbedding.walkArc dual t) 1 ∧
          D.primalEmbedding.coordinates
            (D.dualEmbedding.walkArc dual t) 1 < d

/-- Every rectangle `(a, b) × (c, d)` is crossed horizontally by an open dual walk. -/
def HasOpenComplementaryDualTransverseWalks
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V)) : Prop :=
  ∀ a b c d : Real, a < b → c < d →
    D.HasOpenComplementaryDualTransverseWalkAt omega a b c d

/-- Joined open primal arms in a strip and open dual horizontal crossings of every rectangle
cannot occur together. -/
theorem not_primalBarrierReady_and_complementaryDualTransverseWalks
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V)) :
    ¬(D.primalEmbedding.primalHalfPlaneBarrierReady omega ∧
      D.HasOpenComplementaryDualTransverseWalks omega) := by
  rintro ⟨hbarrier, htransverse⟩
  obtain ⟨a, b, c, d, hab, hcd, xl, xu, xj, lower, upper,
    hlowerNil, hupperNil, hlowerOpen, hupperOpen,
    hlowerBottom, hupperTop, hlowerX, hupperX⟩ := hbarrier
  obtain ⟨yl, yr, dual, hdualNil, hdualOpen, hdualLeft,
    hdualRight, hdualY⟩ := htransverse a b c d hab hcd
  exact D.no_open_dual_transverse_walk_of_joined_primal_arms
    omega hab hcd lower upper dual hlowerNil hupperNil hdualNil
    hlowerOpen hupperOpen hdualOpen hdualLeft hdualRight
    hlowerBottom hupperTop hlowerX hupperX hdualY

end PeriodicPlanarDualPair

end StatMech.FK.PeriodicPlanar

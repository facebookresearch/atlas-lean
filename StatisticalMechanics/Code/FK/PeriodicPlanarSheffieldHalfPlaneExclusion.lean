/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArmsHighProbability
import Code.FK.PeriodicPlanarSheffieldHalfPlaneBarrier











open MeasureTheory Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}



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

namespace PeriodicPlanarDualPair



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




def HasOpenComplementaryDualTransverseWalks
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V)) : Prop :=
  ∀ a b c d : Real, a < b → c < d →
    D.HasOpenComplementaryDualTransverseWalkAt omega a b c d



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

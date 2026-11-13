/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldDeepConnectorRows
import Code.FK.PeriodicPlanarSheffieldExclusion
import Code.FK.PeriodicPlanarDualBurtonKeane





open MeasureTheory Set

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair



structure SymmetricBandDeepConnectorCageCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    (B rPrimal Rdeep rDual : Real) (band width : Nat)
    (L U : Finset V) where
  Rcage : Real
  C : Real
  D0 : Real
  A : Real
  Tbottom : Real
  Ttop : Real
  rightGap : C - 4 * B + B < D0 + 4 * B
  lowerSources : ∀ x ∈ L,
    D.primalEmbedding.vertexCoord x 1 < C - 4 * B
  upperSources : ∀ y ∈ U,
    D0 + 4 * B < D.primalEmbedding.vertexCoord y 1
  width_eq : A + 4 * B = Rdeep ∧
    Rdeep + width = Rcage - 4 * B
  lowerCorridor :
    D.primalEmbedding.infiniteOpenBoundaryConnectionTo
        rPrimal (L : Set V)
        (D.primalEmbedding.lowerBoundaryRayVertices
          rPrimal (-(band : Real))) ⊆
      D.primalEmbedding.horizontalCrossingEvent
        (rDual - 5 * B) (Rcage + 5 * B)
        (C + 4 * B) (Tbottom - 4 * B)
  upperCorridor :
    D.primalEmbedding.infiniteOpenBoundaryConnectionTo
        rPrimal (U : Set V)
        (D.primalEmbedding.upperBoundaryRayVertices rPrimal band) ⊆
      D.primalEmbedding.horizontalCrossingEvent
        (rDual - 5 * B) (Rcage + 5 * B)
        (Ttop + 4 * B) (D0 - 4 * B)
  dual_left_lt_right : rDual < Rcage
  rightWidth : A + 10 * B < Rcage
  bottomGap : C + 10 * B < Tbottom
  topGap : Ttop + 10 * B < D0
  rootRight : rDual + B ≤ A
  rootBottom : Tbottom < -(band : Real)
  rootTop : (band : Real) < Ttop
  rectBottom : C ≤ -(band : Real)
  rectTop : (band : Real) ≤ D0



theorem SymmetricBandDeepConnectorCageCertificate.disjoint_boundaryBand
    {B rPrimal Rdeep rDual : Real} {band width : Nat}
    {L U : Finset V}
    (cert : SymmetricBandDeepConnectorCageCertificate D
      B rPrimal Rdeep rDual band width L U)
    (hBpos : 0 < B)
    (hBp : ∀ {v w : V} (hvw : P.graph.Adj v w) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hvw t -
          D.primalEmbedding.vertex v) i| ≤ B)
    (hBd : ∀ {v w : W} (hvw : Pdual.graph.Adj v w) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hvw t -
          D.dualEmbedding.vertex v) i| ≤ B) :
    Disjoint
      (D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent
        rPrimal Rdeep (-(band : Real)) band width L U)
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
          rDual (-(band : Real)) band) := by
  have hsubset :=
    D.finiteDeepOpenExitedJoinedBoundaryArmEvent_subset_threeCrossingCageEvent
      hBp hBpos.le cert.rightGap cert.lowerSources cert.upperSources
        cert.width_eq cert.lowerCorridor cert.upperCorridor
  exact
    D.finiteDeepOpenExitedJoinedBoundaryArmEvent_disjoint_boundaryBand_of_subset_cage
      hBpos hBp hBd cert.dual_left_lt_right cert.rightWidth
        cert.bottomGap cert.topGap cert.rootRight cert.rootBottom
        cert.rootTop cert.rectBottom cert.rectTop hsubset




theorem complementaryDual_rightHalfPlane_measure_eq_zero_of_symmetricBandCages
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hdualErgodic : Pdual.IsErgodic (D.dualMeasure mu))
    (hdualUnique : D.dualMeasure mu
      {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    {B : Real} (hBpos : 0 < B)
    (hBp : ∀ {v w : V} (hvw : P.graph.Adj v w) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hvw t -
          D.primalEmbedding.vertex v) i| ≤ B)
    (hBd : ∀ {v w : W} (hvw : Pdual.graph.Adj v w) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hvw t -
          D.dualEmbedding.vertex v) i| ≤ B)
    (rDual : Real) {rPrimal Rdeep : Real} (hrR : rPrimal ≤ Rdeep)
    (hcage : ∀ (band : Nat) (L U : Finset V) (width : Nat),
      (L : Set V) ⊆
          D.primalEmbedding.rightHalfPlaneVertices Rdeep →
      (U : Set V) ⊆
          D.primalEmbedding.rightHalfPlaneVertices Rdeep →
      U = L.image
          (P.shift (verticalShift (1 + 2 * (band : Int)))) →
      SymmetricBandDeepConnectorCageCertificate D
        B rPrimal Rdeep rDual band width L U) :
    D.dualMeasure mu
      (D.dualEmbedding.rightHalfPlaneHasInfiniteCluster rDual) = 0 := by
  apply D.complementaryDual_rightHalfPlane_measure_eq_zero_of_separatedRows
    mu hFKG hTI hunique hdualErgodic hdualUnique rDual hrR
      (fun band => -(band : Real)) (fun band => 2 * (band : Int))
  intro band L U width hL hU htranslate
  have hcert := hcage band L U width hL hU (by
    simpa only [mul_comm] using htranslate)
  have hdisjoint := hcert.disjoint_boundaryBand hBpos hBp hBd
  have hheight : (-(band : Real)) + (2 * (band : Int) : Int) =
      (band : Real) := by
    push_cast
    ring
  simpa only [hheight] using hdisjoint




theorem freeBufferedInfiniteVolume_complementaryDual_rightHalfPlane_zero_of_symmetricBandCages
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hcommon :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1)
    {B : Real} (hBpos : 0 < B)
    (hBp : ∀ {v w : V} (hvw : P.graph.Adj v w) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hvw t -
          D.primalEmbedding.vertex v) i| ≤ B)
    (hBd : ∀ {v w : W} (hvw : Pdual.graph.Adj v w) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hvw t -
          D.dualEmbedding.vertex v) i| ≤ B)
    (rDual : Real) {rPrimal Rdeep : Real} (hrR : rPrimal ≤ Rdeep)
    (hcage : ∀ (band : Nat) (L U : Finset V) (width : Nat),
      (L : Set V) ⊆
          D.primalEmbedding.rightHalfPlaneVertices Rdeep →
      (U : Set V) ⊆
          D.primalEmbedding.rightHalfPlaneVertices Rdeep →
      U = L.image
          (P.shift (verticalShift (1 + 2 * (band : Int)))) →
      SymmetricBandDeepConnectorCageCertificate D
        B rPrimal Rdeep rDual band width L U) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    D.dualMeasure mu
      (D.dualEmbedding.rightHalfPlaneHasInfiniteCluster rDual) = 0 := by
  let mu : Measure (ConfigSpace (Sym2 V)) :=
    P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
  letI : IsProbabilityMeasure mu := inferInstance
  have hFKG : IsFKG mu :=
    P.freeBufferedInfiniteVolume_isFKG hp hp1 hq
  have hTI : P.IsTranslationInvariant mu :=
    P.freeBufferedInfiniteVolume_isTranslationInvariant hp hp1 hq
  have hunique := D.primalUnique_measure_eq_one_of_common mu hcommon
  have hdualUnique := D.dualUnique_measure_eq_one_of_common mu hcommon
  have hergodic :=
    D.primalEmbedding.freeBufferedInfiniteVolume_isErgodic hp hp1 hq
  have hdualErgodic := D.dualMeasure_isErgodic mu hergodic
  exact D.complementaryDual_rightHalfPlane_measure_eq_zero_of_symmetricBandCages
    mu hFKG hTI hunique hdualErgodic hdualUnique hBpos hBp hBd
      rDual hrR hcage

end PeriodicPlanarDualPair

end StatMech.FK.PeriodicPlanar

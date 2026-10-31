/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.DeepConnectorRows
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.TemplateCrossings
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.DualBurtonKeane

/-!
# Cage certificates for symmetric bands

Geometric certificates placing finite deep connectors inside a three-crossing cage around the
boundary band `[-band, band]`, and the half-plane statements they would imply.

## i. Overview

A `SymmetricBandDeepConnectorCageCertificate` records the cage parameters and the inclusions
and inequalities needed by
`finiteDeepOpenExitedJoinedBoundaryArmEvent_disjoint_boundaryBand_of_subset_cage`; its
`disjoint_boundaryBand` gives the disjointness hypothesis of
`complementaryDual_rightHalfPlane_measure_eq_zero_of_separatedRows`. The two headline results
assume a certificate for every band and every admissible source row `L` (hypothesis `hcage`).

Vacuity. `hcage` cannot hold when `0 ≤ B` and `V` is nonempty: placing a single source vertex
at height `≥ 0` in the deep half-plane, the certificate fields `lowerSources` and `rectBottom`
force its height below `-band ≤ 0`. This is proved in Lean as
`PeriodicPlanarDualPair.false_of_forall_symmetricBandDeepConnectorCageCertificate`. Both headline
results assume `0 < B` and a measure with a unique infinite cluster (so `V` is nonempty), hence
they are vacuous.

## ii. Key results

- `PeriodicPlanarDualPair.SymmetricBandDeepConnectorCageCertificate`.
- `PeriodicPlanarDualPair.false_of_forall_symmetricBandDeepConnectorCageCertificate` : the
  certificate family is empty (refutation of `hcage`).
- `complementaryDual_rightHalfPlane_measure_eq_zero_of_symmetricBandCages`,
  `freeBufferedInfiniteVolume_complementaryDual_rightHalfPlane_zero_of_symmetricBandCages` :
  vacuous (hypothesis `hcage` refuted).

## iii. Table of contents

- A. Cage certificates
- B. The dual half-plane from cage certificates

## iv. References

- S. Sheffield, *Random Surfaces*, Astérisque 304 (2005), Ch. 9.
-/

@[expose] public section

open MeasureTheory Set

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

variable {V W : Type} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair

/-! ## A. Cage certificates -/

/-- Cage data for the band `[-band, band]`: rectangle and corridor parameters, the corridor
inclusions of the two arm events, and the inequalities needed to place the finite deep connector
inside a three-crossing cage. For a source row at height `≥ 0` no certificate exists when `0 ≤ B`,
see `false_of_forall_symmetricBandDeepConnectorCageCertificate`. -/
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

/-- The cage-certificate family assumed by
`complementaryDual_rightHalfPlane_measure_eq_zero_of_symmetricBandCages` does not exist when
`0 ≤ B` and `V` is nonempty: for a source vertex at height `≥ 0` in the deep half-plane,
`lowerSources` and `rectBottom` force its height below `C - 4 * B ≤ -band ≤ 0`. -/
lemma false_of_forall_symmetricBandDeepConnectorCageCertificate
    (D : PeriodicPlanarDualPair P Pdual) {B rPrimal Rdeep rDual : Real} (hB : 0 ≤ B)
    (x0 : V)
    (hcage : ∀ (band : Nat) (L U : Finset V) (width : Nat),
      (L : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices Rdeep →
      (U : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices Rdeep →
      U = L.image (P.shift (verticalShift (1 + 2 * (band : Int)))) →
      SymmetricBandDeepConnectorCageCertificate D B rPrimal Rdeep rDual band width L U) :
    False := by
  let z : Site 2 := ![⌈Rdeep - D.primalEmbedding.vertexCoord x0 0⌉,
    ⌈-D.primalEmbedding.vertexCoord x0 1⌉]
  let x : V := P.shift z x0
  have hx0 : Rdeep ≤ D.primalEmbedding.vertexCoord x 0 := by
    have h := Int.le_ceil (Rdeep - D.primalEmbedding.vertexCoord x0 0)
    simp only [x, PeriodicPlaneEmbedding.vertexCoord_shift, z, Matrix.cons_val_zero]
    linarith
  have hx1 : 0 ≤ D.primalEmbedding.vertexCoord x 1 := by
    have h := Int.le_ceil (-D.primalEmbedding.vertexCoord x0 1)
    simp only [x, PeriodicPlaneEmbedding.vertexCoord_shift, z, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    linarith
  have hL : (({x} : Finset V) : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices Rdeep := by
    intro y hy
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at hy
    subst hy
    exact hx0
  have hU : ((({x} : Finset V).image
      (P.shift (verticalShift (1 + 2 * ((0 : Nat) : Int))))) : Set V) ⊆
        D.primalEmbedding.rightHalfPlaneVertices Rdeep := by
    intro y hy
    rw [Finset.coe_image, Finset.coe_singleton, Set.image_singleton,
      Set.mem_singleton_iff] at hy
    subst hy
    change Rdeep ≤ D.primalEmbedding.vertexCoord _ 0
    rw [PeriodicPlaneEmbedding.vertexCoord_shift, verticalShift_zero_apply]
    simpa using hx0
  have cert := hcage 0 {x} _ 0 hL hU rfl
  have h1 := cert.lowerSources x (Finset.mem_singleton_self x)
  have h2 := cert.rectBottom
  push_cast at h2
  linarith

/-- A cage certificate makes the finite deep connector disjoint from the dual band event. -/
lemma SymmetricBandDeepConnectorCageCertificate.disjoint_boundaryBand
    {D : PeriodicPlanarDualPair P Pdual} {B rPrimal Rdeep rDual : Real} {band width : Nat}
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

/-! ## B. The dual half-plane from cage certificates -/

/-- No dual infinite cluster in `{x ≥ rDual}`, given cage certificates for every band and source
row. Vacuous: the hypothesis `hcage` is refuted by
`false_of_forall_symmetricBandDeepConnectorCageCertificate`. -/
lemma complementaryDual_rightHalfPlane_measure_eq_zero_of_symmetricBandCages
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

/-- The previous statement for the free buffered infinite-volume FK measure with coexisting unique
clusters. Vacuous: the hypothesis `hcage` is refuted by
`false_of_forall_symmetricBandDeepConnectorCageCertificate`. -/
lemma freeBufferedInfiniteVolume_complementaryDual_rightHalfPlane_zero_of_symmetricBandCages
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
  let : IsProbabilityMeasure mu := inferInstance
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

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
`complementaryDual_rightHalfPlane_measure_eq_zero_of_separatedRows`.

Vacuity. A certificate family for every band and every admissible source row `L`
(hypothesis `hcage`) cannot hold when `0 ≤ B` and `V` is nonempty: placing a single source
vertex at height `≥ 0` in the deep half-plane, the certificate fields `lowerSources` and
`rectBottom` force its height below `-band ≤ 0`. This is proved in Lean as
`PeriodicPlanarDualPair.false_of_forall_symmetricBandDeepConnectorCageCertificate`. The two
headline wrappers that assumed `hcage` were therefore removed as vacuous; the certificate,
its refutation, and the single-certificate disjointness lemma are retained.

## ii. Key results

- `PeriodicPlanarDualPair.SymmetricBandDeepConnectorCageCertificate`.
- `PeriodicPlanarDualPair.false_of_forall_symmetricBandDeepConnectorCageCertificate` : the
  certificate family is empty (refutation of `hcage`).
- `PeriodicPlanarDualPair.SymmetricBandDeepConnectorCageCertificate.disjoint_boundaryBand` :
  a single cage certificate gives the disjointness hypothesis of the separated-rows result.

## iii. Table of contents

- A. Cage certificates

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

/-- No cage-certificate family covers every band and source row when
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

end PeriodicPlanarDualPair

end StatMech.FK.PeriodicPlanar

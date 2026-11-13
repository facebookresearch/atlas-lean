/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldPairedRecurrence
import Code.FK.PeriodicPlanarStrictNoCoexistenceClosure
import Code.FK.PeriodicPlanarCriticalNontriviality










open Filter MeasureTheory Set Topology

namespace StatMech.FK.PeriodicPlanar

open Lattice BeffaraDC

variable {V W : Type} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}





structure PeriodicPlanarDualPair.ExpandedEndpointSheffieldCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) where
  B : Real
  Bpos : 0 < B
  primalArcBound : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
    |D.primalEmbedding.coordinates
      (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B
  dualArcBound : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
    |D.dualEmbedding.coordinates
      (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B
  template : Nat -> Finset V
  radius : Nat -> Nat
  step : Nat -> Int
  vLeft : Nat -> Real
  vRight : Nat -> Real
  vBottom : Nat -> Real
  vTop : Nat -> Real
  hLeft : Nat -> Real
  hRight : Nat -> Real
  hBottom : Nat -> Real
  hTop : Nat -> Real
  pad : Nat -> Real
  level : ExpandedEndpointPrimalBoundaryBandLevel D.primalEmbedding mu
    template radius vLeft vRight vBottom vTop pad
  continuation :
    D.primalEmbedding.UniformTemplateAdjacentBoundaryBandCrossingRadius
      mu template step radius
  alignLeft : forall n, hLeft n + pad n = vLeft n - pad n
  alignRight : forall n, hRight n - pad n = vRight n + pad n
  alignBottom : forall n, hBottom n - pad n = vBottom n + pad n
  alignTop : forall n, hTop n + pad n = vTop n - pad n + step n
  pad_ge : forall n, 4 * B <= pad n
  verticalWidth : forall n, 10 * B < vRight n - vLeft n
  verticalHeight : forall n, 10 * B < vTop n - vBottom n
  horizontalWidth : forall n, 10 * B < hRight n - hLeft n
  horizontalHeight : forall n, 10 * B < hTop n - hBottom n
  dualVertical : Tendsto (fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (vLeft n) (vRight n) (vBottom n) (vTop n))) atTop (nhds 1)
  dualHorizontal : Tendsto (fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (hLeft n) (hRight n) (hBottom n) (hTop n))) atTop (nhds 1)


theorem PeriodicPlanarDualPair.ExpandedEndpointSheffieldCertificate.false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (data : D.ExpandedEndpointSheffieldCertificate mu) : False := by
  exact data.level.false_of_alignedEndpoints D mu data.continuation
    data.alignLeft data.alignRight data.alignBottom data.alignTop
    data.B data.Bpos data.primalArcBound data.dualArcBound data.pad_ge
    data.verticalWidth data.verticalHeight data.horizontalWidth
    data.horizontalHeight data.dualVertical data.dualHorizontal







structure PeriodicPlanarDualPair.BranchAlignedOutwardEndpointCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) where
  B : Real
  Bpos : 0 < B
  primalArcBound : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
    |D.primalEmbedding.coordinates
      (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B
  dualArcBound : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
    |D.dualEmbedding.coordinates
      (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B
  branch : Nat -> Bool
  a : Nat -> Real
  b : Nat -> Real
  c : Nat -> Real
  d : Nat -> Real
  xPad : Nat -> Real
  yPad : Nat -> Real
  vLeft : Nat -> Real
  vRight : Nat -> Real
  vBottom : Nat -> Real
  vTop : Nat -> Real
  hLeft : Nat -> Real
  hRight : Nat -> Real
  hBottom : Nat -> Real
  hTop : Nat -> Real
  vLeft_eq : forall n, vLeft n = a n + xPad n
  vRight_eq : forall n, vRight n = b n - xPad n
  vBottom_eq : forall n, vBottom n = c n
  vTop_eq : forall n, vTop n = d n
  hLeft_eq : forall n, hLeft n = a n
  hRight_eq : forall n, hRight n = b n
  hBottom_eq : forall n, hBottom n = c n + yPad n
  hTop_eq : forall n, hTop n = d n - yPad n
  xPad_ge : forall n, 4 * B <= xPad n
  yPad_ge : forall n, 4 * B <= yPad n
  outerWidth : forall n, a n + 5 * B < b n - 5 * B
  outerHeight : forall n, c n + 5 * B < d n - 5 * B
  primalSelected : Tendsto (fun n => if branch n then
    mu.real (D.primalEmbedding.verticalCrossingEvent
      (vLeft n) (vRight n) (vBottom n) (vTop n))
  else
    mu.real (D.primalEmbedding.horizontalCrossingEvent
      (hLeft n) (hRight n) (hBottom n) (hTop n))) atTop (nhds 1)
  dualSelected : Tendsto (fun n => if branch n then
    mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (hLeft n) (hRight n) (hBottom n) (hTop n))
  else
    mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (vLeft n) (vRight n) (vBottom n) (vTop n))) atTop (nhds 1)


theorem PeriodicPlanarDualPair.BranchAlignedOutwardEndpointCertificate.false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (data : D.BranchAlignedOutwardEndpointCertificate mu) : False := by
  exact D.outwardBranchAlignedComplementary_false mu data.B data.Bpos
    data.primalArcBound data.dualArcBound data.branch
    data.a data.b data.c data.d data.xPad data.yPad
    data.vLeft data.vRight data.vBottom data.vTop
    data.hLeft data.hRight data.hBottom data.hTop
    data.vLeft_eq data.vRight_eq data.vBottom_eq data.vTop_eq
    data.hLeft_eq data.hRight_eq data.hBottom_eq data.hTop_eq
    data.xPad_ge data.yPad_ge data.outerWidth data.outerHeight
    data.primalSelected data.dualSelected



theorem PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_branchAlignedOutwardEndpointCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (hcertificate :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 ->
        Nonempty (D.BranchAlignedOutwardEndpointCertificate mu)) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
  dsimp only
  intro hcommon
  obtain ⟨data⟩ := hcertificate hcommon
  exact data.false D _



theorem PeriodicPlanarDualPair.strictDualNoCoexistence_of_branchAlignedOutwardEndpointCertificate_logisticCylinders
    (D : PeriodicPlanarDualPair P Pdual)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real} (hq : 1 <= q)
    (hcertificate : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 ->
        Nonempty (D.BranchAlignedOutwardEndpointCertificate mu))
    (hagrees :
      P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
    StrictDualNoCoexistence
      (fun p => P.wiredPercolates p q)
      (fun p => Pdual.wiredPercolates p q) q := by
  apply D.strictDualNoCoexistence_of_sheffieldNotFull_logisticCylinders
    hconn hconnDual hq
  · intro p hp hp1
    exact D.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_branchAlignedOutwardEndpointCertificate
      hp hp1 hq (hcertificate p hp hp1)
  · exact hagrees



theorem PeriodicPlanarDualPair.dualCritical_relation_of_decay_branchAlignedOutwardEndpointCertificate_logisticCylinders
    (D : PeriodicPlanarDualPair P Pdual)
    (H : PolynomialConnectionShells D)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real} (hq : 1 <= q)
    (hcoverage : DualSubcriticalCoverage
      (fun r => Pdual.wiredPercolates r q) (P.criticalPoint q) q)
    (hcoverageDual : DualSubcriticalCoverage
      (fun r => P.wiredPercolates r q) (Pdual.criticalPoint q) q)
    (hdecay : SubcriticalTwoPointExponentialDecay P q (P.criticalPoint q))
    (hcertificate : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 ->
        Nonempty (D.BranchAlignedOutwardEndpointCertificate mu))
    (hagrees :
      P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
    dualParam (P.criticalPoint q) q = Pdual.criticalPoint q /\
      (P.criticalPoint q / (1 - P.criticalPoint q)) *
        (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
  obtain ⟨hpc, hpcDual⟩ :=
    P.criticalPoints_mem_Ioo_of_bidirectionalCoverage_qge_one
      Pdual hq hcoverage hcoverageDual
  apply D.dualCritical_relation_of_decay_sheffieldNotFull_logisticCylinders
    H hconn hconnDual hpc hpcDual hq hdecay
  · intro p hp hp1
    exact D.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_branchAlignedOutwardEndpointCertificate
      hp hp1 hq (hcertificate p hp hp1)
  · exact hagrees



theorem PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_expandedEndpointCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (hcertificate :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 ->
        Nonempty (D.ExpandedEndpointSheffieldCertificate mu)) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
  dsimp only
  intro hcommon
  obtain ⟨data⟩ := hcertificate hcommon
  exact data.false D _



theorem PeriodicPlanarDualPair.strictDualNoCoexistence_of_expandedEndpointCertificate_logisticCylinders
    (D : PeriodicPlanarDualPair P Pdual)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real} (hq : 1 <= q)
    (hcertificate : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 ->
        Nonempty (D.ExpandedEndpointSheffieldCertificate mu))
    (hagrees :
      P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
    StrictDualNoCoexistence
      (fun p => P.wiredPercolates p q)
      (fun p => Pdual.wiredPercolates p q) q := by
  apply D.strictDualNoCoexistence_of_sheffieldNotFull_logisticCylinders
    hconn hconnDual hq
  · intro p hp hp1
    exact D.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_expandedEndpointCertificate
      hp hp1 hq (hcertificate p hp hp1)
  · exact hagrees



theorem PeriodicPlanarDualPair.dualCritical_relation_of_decay_expandedEndpointCertificate_logisticCylinders
    (D : PeriodicPlanarDualPair P Pdual)
    (H : PolynomialConnectionShells D)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real} (hq : 1 <= q)
    (hcoverage : DualSubcriticalCoverage
      (fun r => Pdual.wiredPercolates r q) (P.criticalPoint q) q)
    (hcoverageDual : DualSubcriticalCoverage
      (fun r => P.wiredPercolates r q) (Pdual.criticalPoint q) q)
    (hdecay : SubcriticalTwoPointExponentialDecay P q (P.criticalPoint q))
    (hcertificate : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 ->
        Nonempty (D.ExpandedEndpointSheffieldCertificate mu))
    (hagrees :
      P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
    dualParam (P.criticalPoint q) q = Pdual.criticalPoint q /\
      (P.criticalPoint q / (1 - P.criticalPoint q)) *
        (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
  obtain ⟨hpc, hpcDual⟩ :=
    P.criticalPoints_mem_Ioo_of_bidirectionalCoverage_qge_one
      Pdual hq hcoverage hcoverageDual
  apply D.dualCritical_relation_of_decay_sheffieldNotFull_logisticCylinders
    H hconn hconnDual hpc hpcDual hq hdecay
  · intro p hp hp1
    exact D.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_expandedEndpointCertificate
      hp hp1 hq (hcertificate p hp hp1)
  · exact hagrees

end StatMech.FK.PeriodicPlanar

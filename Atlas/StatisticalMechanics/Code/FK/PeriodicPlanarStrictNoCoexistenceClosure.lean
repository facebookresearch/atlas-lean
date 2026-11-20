/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarStrictNoCoexistenceCapstone
import Code.FK.PeriodicPlanarSheffieldExclusion
import Code.FK.SecantClose













open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC

variable {V W : Type} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}



noncomputable def PeriodicGraph.freeBufferedBoundaryCylinderProbability
    (P : PeriodicGraph V) (n : Nat) (p q : Real) : Real :=
  if h : p ∈ Ioo (0 : Real) 1 ∧ 0 < q then
    (P.freeBufferedInfiniteVolume h.1.1 h.1.2 h.2 :
      Measure (ConfigSpace (Sym2 V))).real
        (P.bufferedCylinder n (P.bufferedRootBoundaryEvent n))
  else 0



noncomputable def PeriodicGraph.wiredBufferedBoundaryCylinderProbability
    (P : PeriodicGraph V) (n : Nat) (p q : Real) : Real :=
  if h : p ∈ Ioo (0 : Real) 1 ∧ 0 < q then
    (P.wiredBufferedInfiniteVolume h.1.1 h.1.2 h.2 :
      Measure (ConfigSpace (Sym2 V))).real
        (P.bufferedCylinder n (P.bufferedRootBoundaryEvent n))
  else 0




noncomputable def PeriodicGraph.freeBufferedCylinderProbability
    (P : PeriodicGraph V) (n : Nat)
    (S : Set (ConfigSpace (Sym2 (P.BufferedVertex n))))
    (p q : Real) : Real :=
  if h : p ∈ Ioo (0 : Real) 1 ∧ 0 < q then
    (P.freeBufferedInfiniteVolume h.1.1 h.1.2 h.2 :
      Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder n S)
  else 0



noncomputable def PeriodicGraph.wiredBufferedCylinderProbability
    (P : PeriodicGraph V) (n : Nat)
    (S : Set (ConfigSpace (Sym2 (P.BufferedVertex n))))
    (p q : Real) : Real :=
  if h : p ∈ Ioo (0 : Real) 1 ∧ 0 < q then
    (P.wiredBufferedInfiniteVolume h.1.1 h.1.2 h.2 :
      Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder n S)
  else 0




def PeriodicGraph.FreeWiredIncreasingCylinderAgreementOffCountable
    (P : PeriodicGraph V) (q : Real) : Prop :=
  ∀ n : Nat,
    {p : Real | ∃ S : Set (ConfigSpace (Sym2 (P.BufferedVertex n))),
      IsIncreasing S ∧
        P.freeBufferedCylinderProbability n S p q ≠
          P.wiredBufferedCylinderProbability n S p q}.Countable



def PeriodicGraph.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic
    (P : PeriodicGraph V) (q : Real) : Prop :=
  ∀ n : Nat,
    {t : Real | ∃ S : Set (ConfigSpace (Sym2 (P.BufferedVertex n))),
      IsIncreasing S ∧
        P.freeBufferedCylinderProbability n S (fsc_logistic t) q ≠
          P.wiredBufferedCylinderProbability n S (fsc_logistic t) q}.Countable




theorem PeriodicGraph.freeWiredIncreasingCylinderAgreementOffCountable_of_logistic
    (P : PeriodicGraph V) {q : Real}
    (hagrees : P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
    P.FreeWiredIncreasingCylinderAgreementOffCountable q := by
  intro n
  apply ((hagrees n).image fsc_logistic).mono
  intro p hp
  have hphysical : p ∈ Ioo (0 : Real) 1 ∧ 0 < q := by
    by_contra hnot
    obtain ⟨S, hS, hne⟩ := hp
    apply hne
    simp only [PeriodicGraph.freeBufferedCylinderProbability,
      PeriodicGraph.wiredBufferedCylinderProbability, dif_neg hnot]
  refine ⟨fsc_logit p, ?_, fsc_logistic_logit hphysical.1.1 hphysical.1.2⟩
  obtain ⟨S, hS, hne⟩ := hp
  refine ⟨S, hS, ?_⟩
  simpa only [fsc_logistic_logit hphysical.1.1 hphysical.1.2] using hne





def PeriodicGraph.FreeWiredBoundaryCylinderAgreementOffCountable
    (P : PeriodicGraph V) (q : Real) : Prop :=
  ∀ n : Nat,
    {p : Real |
      P.freeBufferedBoundaryCylinderProbability n p q ≠
        P.wiredBufferedBoundaryCylinderProbability n p q}.Countable



theorem PeriodicGraph.freeWiredBoundaryCylinderAgreementOffCountable_of_increasingCylinders
    (P : PeriodicGraph V) {q : Real}
    (hagrees : P.FreeWiredIncreasingCylinderAgreementOffCountable q) :
    P.FreeWiredBoundaryCylinderAgreementOffCountable q := by
  intro n
  apply (hagrees n).mono
  intro p hp
  refine ⟨P.bufferedRootBoundaryEvent n,
    P.bufferedRootBoundaryEvent_isIncreasing n, ?_⟩
  simpa only [PeriodicGraph.freeBufferedBoundaryCylinderProbability,
    PeriodicGraph.wiredBufferedBoundaryCylinderProbability,
    PeriodicGraph.freeBufferedCylinderProbability,
    PeriodicGraph.wiredBufferedCylinderProbability] using hp





theorem PeriodicGraph.freeWiredPercolationAgreementOffCountable_of_boundaryCylinders
    (P : PeriodicGraph V) {q : Real}
    (hcyl : P.FreeWiredBoundaryCylinderAgreementOffCountable q) :
    P.FreeWiredPercolationAgreementOffCountable q := by
  let exceptional : Set Real := ⋃ n : Nat,
    {p : Real |
      P.freeBufferedBoundaryCylinderProbability n p q ≠
        P.wiredBufferedBoundaryCylinderProbability n p q}
  refine ⟨exceptional, Set.countable_iUnion hcyl, ?_⟩
  intro p hp hpExceptional
  by_cases hq : 0 < q
  · have heq (n : Nat) :
        P.freeBufferedBoundaryCylinderProbability n p q =
          P.wiredBufferedBoundaryCylinderProbability n p q := by
      by_contra hne
      apply hpExceptional
      exact Set.mem_iUnion.2 ⟨n, hne⟩
    have hfree : Tendsto
        (fun n => P.freeBufferedBoundaryCylinderProbability n p q)
        Filter.atTop (nhds (P.freeBufferedPercolationProbability p q)) := by
      apply (P.freeBufferedRootBoundaryCylinder_real_tendsto
        hp.1 hp.2 hq).congr'
      filter_upwards with n
      rw [PeriodicGraph.freeBufferedBoundaryCylinderProbability,
        dif_pos ⟨hp, hq⟩]
    have hwired : Tendsto
        (fun n => P.wiredBufferedBoundaryCylinderProbability n p q)
        Filter.atTop (nhds (P.wiredPercolationProbability p q)) := by
      apply (P.bufferedRootBoundaryCylinder_real_tendsto
        hp.1 hp.2 hq).congr'
      filter_upwards with n
      rw [PeriodicGraph.wiredBufferedBoundaryCylinderProbability,
        dif_pos ⟨hp, hq⟩]
    have hwiredOnFree : Tendsto
        (fun n => P.freeBufferedBoundaryCylinderProbability n p q)
        Filter.atTop (nhds (P.wiredPercolationProbability p q)) :=
      hwired.congr' (Filter.Eventually.of_forall fun n => (heq n).symm)
    exact tendsto_nhds_unique hfree hwiredOnFree
  · rw [PeriodicGraph.freeBufferedPercolationProbability,
      PeriodicGraph.wiredPercolationProbability,
      dif_neg (fun h => hq h.2), dif_neg (fun h => hq h.2)]



theorem PeriodicGraph.freeWiredPercolationAgreementOffCountable_of_increasingCylinders
    (P : PeriodicGraph V) {q : Real}
    (hagrees : P.FreeWiredIncreasingCylinderAgreementOffCountable q) :
    P.FreeWiredPercolationAgreementOffCountable q :=
  P.freeWiredPercolationAgreementOffCountable_of_boundaryCylinders
    (P.freeWiredBoundaryCylinderAgreementOffCountable_of_increasingCylinders
      hagrees)




theorem PeriodicPlanarDualPair.freeCommonNoCoexistence_of_commonUniqueNotFull
    (D : PeriodicPlanarDualPair P Pdual)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real} (hq : 1 ≤ q)
    (hnotFull : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      ((P.freeBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) :
        ProbabilityMeasure (ConfigSpace (Sym2 V))) :
        Measure (ConfigSpace (Sym2 V)))
          D.commonUniqueInfiniteClusterEvent ≠ 1) :
    D.FreeCommonNoCoexistence q := by
  apply D.freeCommonNoCoexistence_of_commonUniqueExclusion
    hconn hconnDual hq
  intro p hp hp1
  exact (D.freeBufferedInfiniteVolume_commonUnique_measure_eq_zero_iff_ne_one
    hp hp1 hq).2 (hnotFull p hp hp1)




theorem PeriodicPlanarDualPair.strictDualNoCoexistence_of_sheffield_offCountableAgreement
    (D : PeriodicPlanarDualPair P Pdual)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real} (hq : 1 ≤ q)
    (hSheffield : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      ((P.freeBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) :
        ProbabilityMeasure (ConfigSpace (Sym2 V))) :
        Measure (ConfigSpace (Sym2 V)))
          D.commonUniqueInfiniteClusterEvent = 0)
    (hagrees : P.FreeWiredPercolationAgreementOffCountable q) :
    StrictDualNoCoexistence
      (fun p => P.wiredPercolates p q)
      (fun p => Pdual.wiredPercolates p q) q := by
  apply D.strictDualNoCoexistence_of_sheffield_and_transfer
    hconn hconnDual hq hSheffield
  exact P.crossParameterWiredToFreeTransfer_of_offCountableAgreement
    hq hagrees




theorem PeriodicPlanarDualPair.strictDualNoCoexistence_of_sheffieldNotFull_offCountableAgreement
    (D : PeriodicPlanarDualPair P Pdual)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real} (hq : 1 ≤ q)
    (hnotFull : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      ((P.freeBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) :
        ProbabilityMeasure (ConfigSpace (Sym2 V))) :
        Measure (ConfigSpace (Sym2 V)))
          D.commonUniqueInfiniteClusterEvent ≠ 1)
    (hagrees : P.FreeWiredPercolationAgreementOffCountable q) :
    StrictDualNoCoexistence
      (fun p => P.wiredPercolates p q)
      (fun p => Pdual.wiredPercolates p q) q := by
  apply D.strictDualNoCoexistence_of_freeCommon_and_transfer hq
  · exact D.freeCommonNoCoexistence_of_commonUniqueNotFull
      hconn hconnDual hq hnotFull
  · exact P.crossParameterWiredToFreeTransfer_of_offCountableAgreement
      hq hagrees



theorem PeriodicPlanarDualPair.strictDualNoCoexistence_of_sheffieldNotFull_increasingCylinders
    (D : PeriodicPlanarDualPair P Pdual)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real} (hq : 1 ≤ q)
    (hnotFull : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      ((P.freeBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) :
        ProbabilityMeasure (ConfigSpace (Sym2 V))) :
        Measure (ConfigSpace (Sym2 V)))
          D.commonUniqueInfiniteClusterEvent ≠ 1)
    (hagrees : P.FreeWiredIncreasingCylinderAgreementOffCountable q) :
    StrictDualNoCoexistence
      (fun p => P.wiredPercolates p q)
      (fun p => Pdual.wiredPercolates p q) q :=
  D.strictDualNoCoexistence_of_sheffieldNotFull_offCountableAgreement
    hconn hconnDual hq hnotFull
      (P.freeWiredPercolationAgreementOffCountable_of_increasingCylinders
        hagrees)


theorem PeriodicPlanarDualPair.strictDualNoCoexistence_of_sheffieldNotFull_logisticCylinders
    (D : PeriodicPlanarDualPair P Pdual)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real} (hq : 1 ≤ q)
    (hnotFull : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      ((P.freeBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) :
        ProbabilityMeasure (ConfigSpace (Sym2 V))) :
        Measure (ConfigSpace (Sym2 V)))
          D.commonUniqueInfiniteClusterEvent ≠ 1)
    (hagrees :
      P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
    StrictDualNoCoexistence
      (fun p => P.wiredPercolates p q)
      (fun p => Pdual.wiredPercolates p q) q :=
  D.strictDualNoCoexistence_of_sheffieldNotFull_increasingCylinders
    hconn hconnDual hq hnotFull
      (P.freeWiredIncreasingCylinderAgreementOffCountable_of_logistic hagrees)



theorem PeriodicPlanarDualPair.dualCritical_relation_of_decay_sheffield_offCountable
    (D : PeriodicPlanarDualPair P Pdual)
    (H : PolynomialConnectionShells D)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real}
    (hpc : P.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hpcDual : Pdual.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hq : 1 ≤ q)
    (hdecay : SubcriticalTwoPointExponentialDecay P q (P.criticalPoint q))
    (hSheffield : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      ((P.freeBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) :
        ProbabilityMeasure (ConfigSpace (Sym2 V))) :
        Measure (ConfigSpace (Sym2 V)))
          D.commonUniqueInfiniteClusterEvent = 0)
    (hagrees : P.FreeWiredPercolationAgreementOffCountable q) :
    dualParam (P.criticalPoint q) q = Pdual.criticalPoint q ∧
      (P.criticalPoint q / (1 - P.criticalPoint q)) *
        (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
  apply D.dualCritical_relation_of_exponentialDecay_sheffield
    H hconn hconnDual hpc hpcDual hq hdecay hSheffield
  exact P.crossParameterWiredToFreeTransfer_of_offCountableAgreement
    hq hagrees



theorem PeriodicPlanarDualPair.dualCritical_relation_of_decay_sheffieldNotFull_offCountable
    (D : PeriodicPlanarDualPair P Pdual)
    (H : PolynomialConnectionShells D)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real}
    (hpc : P.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hpcDual : Pdual.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hq : 1 ≤ q)
    (hdecay : SubcriticalTwoPointExponentialDecay P q (P.criticalPoint q))
    (hnotFull : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      ((P.freeBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) :
        ProbabilityMeasure (ConfigSpace (Sym2 V))) :
        Measure (ConfigSpace (Sym2 V)))
          D.commonUniqueInfiniteClusterEvent ≠ 1)
    (hagrees : P.FreeWiredPercolationAgreementOffCountable q) :
    dualParam (P.criticalPoint q) q = Pdual.criticalPoint q ∧
      (P.criticalPoint q / (1 - P.criticalPoint q)) *
        (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
  apply D.dualCritical_relation_of_exponentialDecay_strictNoCoexistence
    H hpc hpcDual hq hdecay
  exact D.strictDualNoCoexistence_of_sheffieldNotFull_offCountableAgreement
    hconn hconnDual hq hnotFull hagrees



theorem PeriodicPlanarDualPair.dualCritical_relation_of_decay_sheffieldNotFull_increasingCylinders
    (D : PeriodicPlanarDualPair P Pdual)
    (H : PolynomialConnectionShells D)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real}
    (hpc : P.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hpcDual : Pdual.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hq : 1 ≤ q)
    (hdecay : SubcriticalTwoPointExponentialDecay P q (P.criticalPoint q))
    (hnotFull : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      ((P.freeBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) :
        ProbabilityMeasure (ConfigSpace (Sym2 V))) :
        Measure (ConfigSpace (Sym2 V)))
          D.commonUniqueInfiniteClusterEvent ≠ 1)
    (hagrees : P.FreeWiredIncreasingCylinderAgreementOffCountable q) :
    dualParam (P.criticalPoint q) q = Pdual.criticalPoint q ∧
      (P.criticalPoint q / (1 - P.criticalPoint q)) *
        (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q :=
  D.dualCritical_relation_of_decay_sheffieldNotFull_offCountable
    H hconn hconnDual hpc hpcDual hq hdecay hnotFull
      (P.freeWiredPercolationAgreementOffCountable_of_increasingCylinders
        hagrees)



theorem PeriodicPlanarDualPair.dualCritical_relation_of_decay_sheffieldNotFull_logisticCylinders
    (D : PeriodicPlanarDualPair P Pdual)
    (H : PolynomialConnectionShells D)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real}
    (hpc : P.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hpcDual : Pdual.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hq : 1 ≤ q)
    (hdecay : SubcriticalTwoPointExponentialDecay P q (P.criticalPoint q))
    (hnotFull : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      ((P.freeBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) :
        ProbabilityMeasure (ConfigSpace (Sym2 V))) :
        Measure (ConfigSpace (Sym2 V)))
          D.commonUniqueInfiniteClusterEvent ≠ 1)
    (hagrees :
      P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
    dualParam (P.criticalPoint q) q = Pdual.criticalPoint q ∧
      (P.criticalPoint q / (1 - P.criticalPoint q)) *
        (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q :=
  D.dualCritical_relation_of_decay_sheffieldNotFull_increasingCylinders
    H hconn hconnDual hpc hpcDual hq hdecay hnotFull
      (P.freeWiredIncreasingCylinderAgreementOffCountable_of_logistic hagrees)

end StatMech.FK.PeriodicPlanar

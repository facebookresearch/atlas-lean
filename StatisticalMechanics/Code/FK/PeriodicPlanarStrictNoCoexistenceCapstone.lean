/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Mathlib.Analysis.Real.Cardinality
import Code.FK.PeriodicPlanarDualBurtonKeane
import Code.FK.PeriodicPlanarStrictCriticalAssembly

open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC

variable {V W : Type} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}




noncomputable def PeriodicGraph.freeBufferedPercolationProbability
    (P : PeriodicGraph V) (p q : Real) : Real :=
  if h : p ∈ Ioo (0 : Real) 1 ∧ 0 < q then
    ((P.freeBufferedInfiniteVolume h.1.1 h.1.2 h.2 :
      ProbabilityMeasure (ConfigSpace (Sym2 V))) :
      Measure (ConfigSpace (Sym2 V))).real P.percolationEvent
  else 0


def PeriodicGraph.FreeBufferedPercolates
    (P : PeriodicGraph V) (p q : Real) : Prop :=
  0 < P.freeBufferedPercolationProbability p q




def PeriodicPlanarDualPair.FreeCommonNoCoexistence
    (D : PeriodicPlanarDualPair P Pdual) (q : Real) : Prop :=
  ∀ p ∈ Ioo (0 : Real) 1,
    ¬ (P.FreeBufferedPercolates p q ∧ D.FreeDualPercolates p q)





def PeriodicGraph.CrossParameterWiredToFreeTransfer
    (P : PeriodicGraph V) (q : Real) : Prop :=
  ∀ r ∈ Ioo (0 : Real) 1, ∀ p ∈ Ioo (0 : Real) 1, r < p ->
    P.wiredPercolates r q -> P.FreeBufferedPercolates p q




def PeriodicGraph.FreeWiredPercolationAgreementOffCountable
    (P : PeriodicGraph V) (q : Real) : Prop :=
  ∃ exceptional : Set Real, exceptional.Countable ∧
    ∀ p ∈ Ioo (0 : Real) 1, p ∉ exceptional ->
      P.freeBufferedPercolationProbability p q =
        P.wiredPercolationProbability p q



theorem PeriodicGraph.freeBufferedMeasure_real_cylinder_monotone_in_p
    (P : PeriodicGraph V) {N m : Nat} (hNm : N ≤ m)
    {p₁ p₂ q : Real} (hp₁ : 0 < p₁) (hp₁' : p₁ < 1)
    (hp₂ : 0 < p₂) (hp₂' : p₂ < 1) (hp₁₂ : p₁ ≤ p₂) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hS : IsIncreasing S) :
    (P.freeBufferedMeasure m hp₁ hp₁' (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) ≤
      (P.freeBufferedMeasure m hp₂ hp₂' (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
  rw [P.freeBufferedMeasure_real_cylinder hNm hp₁ hp₁'
      (zero_lt_one.trans_le hq),
    P.freeBufferedMeasure_real_cylinder hNm hp₂ hp₂'
      (zero_lt_one.trans_le hq)]
  let A := P.bufferedRestrictLE hNm ⁻¹' S
  have hA : IsIncreasing A := fun _ _ home hmem =>
    hS (P.monotone_bufferedRestrictLE hNm home) hmem
  simpa only [bcProb_bot_eq_fkProb] using
    (bcProb_monotone_in_p (P.bufferedGraph m)
      (⊥ : SimpleGraph (P.BufferedVertex m))
      hp₁ hp₁' hp₂ hp₂' hp₁₂ hq hA)



theorem PeriodicGraph.freeBufferedInfiniteVolume_real_cylinder_monotone_in_p
    (P : PeriodicGraph V) (N : Nat)
    {p₁ p₂ q : Real} (hp₁ : 0 < p₁) (hp₁' : p₁ < 1)
    (hp₂ : 0 < p₂) (hp₂' : p₂ < 1) (hp₁₂ : p₁ ≤ p₂) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hS : IsIncreasing S) :
    (P.freeBufferedInfiniteVolume hp₁ hp₁' (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) ≤
      (P.freeBufferedInfiniteVolume hp₂ hp₂' (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
  have hlim₁ := P.freeBufferedMeasure_tendsto_cylinder N hp₁ hp₁' hq hS
  have hlim₂ := P.freeBufferedMeasure_tendsto_cylinder N hp₂ hp₂' hq hS
  apply le_of_tendsto_of_tendsto hlim₁ hlim₂
  filter_upwards [eventually_ge_atTop N] with m hNm
  exact P.freeBufferedMeasure_real_cylinder_monotone_in_p hNm
    hp₁ hp₁' hp₂ hp₂' hp₁₂ hq hS



theorem PeriodicGraph.freeBufferedRootBoundaryCylinder_real_tendsto
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp₁ : p < 1) (hq : 0 < q) :
    Tendsto
      (fun n =>
        (P.freeBufferedInfiniteVolume hp hp₁ hq :
          Measure (ConfigSpace (Sym2 V))).real
          (P.bufferedCylinder n (P.bufferedRootBoundaryEvent n)))
      atTop (nhds (P.freeBufferedPercolationProbability p q)) := by
  let mu : Measure (ConfigSpace (Sym2 V)) :=
    P.freeBufferedInfiniteVolume hp hp₁ hq
  have htend := tendsto_measure_iInter_atTop
    (μ := mu)
    (fun n => (P.bufferedCylinder_measurableSet n
      (P.bufferedRootBoundaryEvent n)).nullMeasurableSet)
    P.bufferedRootBoundaryCylinder_antitone
    ⟨0, measure_ne_top mu _⟩
  rw [P.iInter_bufferedRootBoundaryCylinder] at htend
  have hreal :=
    (ENNReal.tendsto_toReal (measure_ne_top mu P.percolationEvent)).comp htend
  rw [PeriodicGraph.freeBufferedPercolationProbability,
    dif_pos ⟨⟨hp, hp₁⟩, hq⟩]
  simpa only [Function.comp_apply, Measure.real] using hreal



theorem PeriodicGraph.freeBufferedPercolationProbability_monotoneOn
    (P : PeriodicGraph V) {q : Real} (hq : 1 ≤ q) :
    MonotoneOn (fun p => P.freeBufferedPercolationProbability p q)
      (Ioo (0 : Real) 1) := by
  rintro p₁ hp₁ p₂ hp₂ hp₁₂
  apply le_of_tendsto_of_tendsto
    (P.freeBufferedRootBoundaryCylinder_real_tendsto
      hp₁.1 hp₁.2 (zero_lt_one.trans_le hq))
    (P.freeBufferedRootBoundaryCylinder_real_tendsto
      hp₂.1 hp₂.2 (zero_lt_one.trans_le hq))
  exact Filter.Eventually.of_forall fun n =>
    P.freeBufferedInfiniteVolume_real_cylinder_monotone_in_p n
      hp₁.1 hp₁.2 hp₂.1 hp₂.2 hp₁₂ hq
        (P.bufferedRootBoundaryEvent_isIncreasing n)





theorem PeriodicGraph.crossParameterWiredToFreeTransfer_of_monotonicity_agreement
    (P : PeriodicGraph V) {q : Real}
    (hwired : MonotoneOn (fun p => P.wiredPercolationProbability p q)
      (Ioo (0 : Real) 1))
    (hfree : MonotoneOn (fun p => P.freeBufferedPercolationProbability p q)
      (Ioo (0 : Real) 1))
    (hagrees : P.FreeWiredPercolationAgreementOffCountable q) :
    P.CrossParameterWiredToFreeTransfer q := by
  obtain ⟨exceptional, hexceptional, hagree⟩ := hagrees
  intro r hr p hp hrp hrPerc
  have hnotSubset : ¬ Ioo r p ⊆ exceptional := by
    intro hsubset
    have hcountable : (Ioo r p).Countable := hexceptional.mono hsubset
    exact (not_le_of_gt hrp)
      ((Cardinal.Real.Ioo_countable_iff).mp hcountable)
  obtain ⟨s, hs, hsExceptional⟩ := Set.not_subset.mp hnotSubset
  have hsPhysical : s ∈ Ioo (0 : Real) 1 :=
    ⟨hr.1.trans hs.1, hs.2.trans hp.2⟩
  have hsWired : 0 < P.wiredPercolationProbability s q :=
    hrPerc.trans_le (hwired hr hsPhysical hs.1.le)
  have hsFree : 0 < P.freeBufferedPercolationProbability s q := by
    rw [hagree s hsPhysical hsExceptional]
    exact hsWired
  exact hsFree.trans_le (hfree hsPhysical hp hs.2.le)



theorem PeriodicGraph.crossParameterWiredToFreeTransfer_of_offCountableAgreement
    (P : PeriodicGraph V) {q : Real} (hq : 1 ≤ q)
    (hagrees : P.FreeWiredPercolationAgreementOffCountable q) :
    P.CrossParameterWiredToFreeTransfer q :=
  P.crossParameterWiredToFreeTransfer_of_monotonicity_agreement
    (P.wiredPercolationProbability_monotoneOn hq)
    (P.freeBufferedPercolationProbability_monotoneOn hq) hagrees





theorem PeriodicPlanarDualPair.freeCommonNoCoexistence_of_commonUniqueExclusion
    (D : PeriodicPlanarDualPair P Pdual)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real} (hq : 1 ≤ q)
    (hSheffield : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      ((P.freeBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) :
        ProbabilityMeasure (ConfigSpace (Sym2 V))) :
        Measure (ConfigSpace (Sym2 V)))
          D.commonUniqueInfiniteClusterEvent = 0) :
    D.FreeCommonNoCoexistence q := by
  intro p hp hboth
  obtain ⟨hprimal, hdual⟩ := hboth
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hprimal' : 0 <
      (P.freeBufferedInfiniteVolume hp.1 hp.2 hq0 : Measure _).real
        P.percolationEvent := by
    unfold PeriodicGraph.FreeBufferedPercolates
      PeriodicGraph.freeBufferedPercolationProbability at hprimal
    rw [dif_pos ⟨hp, hq0⟩] at hprimal
    exact hprimal
  have hdual' : 0 < (D.dualMeasure
      (P.freeBufferedInfiniteVolume hp.1 hp.2 hq0 : Measure _)).real
        Pdual.percolationEvent := by
    unfold FreeDualPercolates freeDualPercolationProbability at hdual
    rw [dif_pos ⟨hp, hq0⟩] at hdual
    unfold dualMeasure Measure.real
    rw [Measure.map_apply
      (continuous_dualConfigEquiv D.edgeDual).measurable
      (percolationEvent_measurableSet Pdual)]
    exact hdual
  have hone :=
    D.freeBufferedInfiniteVolume_commonUniqueInfiniteClusterEvent_measure_eq_one
      hconn hconnDual hp.1 hp.2 hq hprimal' hdual'
  have hzero := hSheffield p hp.1 hp.2
  rw [hzero] at hone
  exact zero_ne_one hone




theorem PeriodicPlanarDualPair.strictDualNoCoexistence_of_freeCommon_and_transfer
    (D : PeriodicPlanarDualPair P Pdual) {q : Real} (hq : 1 ≤ q)
    (hcommon : D.FreeCommonNoCoexistence q)
    (htransfer : P.CrossParameterWiredToFreeTransfer q) :
    StrictDualNoCoexistence
      (fun p => P.wiredPercolates p q)
      (fun p => Pdual.wiredPercolates p q) q := by
  intro r hr p hp hrp hboth
  have hprimalFree : P.FreeBufferedPercolates p q :=
    htransfer r hr p hp hrp hboth.1
  have hdualFree : D.FreeDualPercolates p q :=
    (D.wiredPercolates_dualParam_iff hp.1 hp.2 hq).mp hboth.2
  exact hcommon p hp ⟨hprimalFree, hdualFree⟩




theorem PeriodicPlanarDualPair.strictDualNoCoexistence_of_sheffield_and_transfer
    (D : PeriodicPlanarDualPair P Pdual)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real} (hq : 1 ≤ q)
    (hSheffield : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      ((P.freeBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) :
        ProbabilityMeasure (ConfigSpace (Sym2 V))) :
        Measure (ConfigSpace (Sym2 V)))
          D.commonUniqueInfiniteClusterEvent = 0)
    (htransfer : P.CrossParameterWiredToFreeTransfer q) :
    StrictDualNoCoexistence
      (fun p => P.wiredPercolates p q)
      (fun p => Pdual.wiredPercolates p q) q := by
  apply D.strictDualNoCoexistence_of_freeCommon_and_transfer hq
  · exact D.freeCommonNoCoexistence_of_commonUniqueExclusion
      hconn hconnDual hq hSheffield
  · exact htransfer





theorem PeriodicPlanarDualPair.dualCritical_relation_of_exponentialDecay_sheffield
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
    (htransfer : P.CrossParameterWiredToFreeTransfer q) :
    dualParam (P.criticalPoint q) q = Pdual.criticalPoint q ∧
      (P.criticalPoint q / (1 - P.criticalPoint q)) *
        (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
  apply D.dualCritical_relation_of_exponentialDecay_strictNoCoexistence
    H hpc hpcDual hq hdecay
  exact D.strictDualNoCoexistence_of_sheffield_and_transfer
    hconn hconnDual hq hSheffield htransfer

end StatMech.FK.PeriodicPlanar

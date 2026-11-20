/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldDeepConnectorCage





open Filter MeasureTheory Set

namespace StatMech.FK.PeriodicPlanar



theorem measure_eq_zero_of_disjoint_measureReal_tendsto_one
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (A : Nat → Set X) (B : Set X) (hB : MeasurableSet B)
    (hdisjoint : ∀ n, Disjoint (A n) B)
    (hA : Tendsto (fun n => mu.real (A n)) atTop (nhds 1)) :
    mu B = 0 := by
  have hsum (n : Nat) : mu.real (A n) + mu.real B ≤ 1 := by
    have hinter : A n ∩ B = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp (hdisjoint n)
    have hadd := measureReal_union_add_inter (μ := mu) hB (s := A n)
    rw [hinter] at hadd
    simp only [measureReal_empty, add_zero] at hadd
    have hunion : mu.real (A n ∪ B) ≤ 1 := measureReal_le_one
    linarith
  have hadd : Tendsto (fun n => mu.real (A n) + mu.real B)
      atTop (nhds (1 + mu.real B)) :=
    hA.add tendsto_const_nhds
  have hlimit : 1 + mu.real B ≤ 1 :=
    le_of_tendsto hadd (Eventually.of_forall hsum)
  have hreal : mu.real B = 0 := by
    exact le_antisymm (by linarith) measureReal_nonneg
  exact ((ENNReal.toReal_eq_zero_iff (mu B)).mp hreal).resolve_right
    (measure_ne_top mu B)

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair



structure FiniteDeepConnectorBandSchedule
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (rDual : Real) (band : Nat) where
  rPrimal : Nat → Real
  Rdeep : Nat → Real
  cArm : Nat → Real
  dArm : Nat → Real
  width : Nat → Nat
  lower : Nat → Finset V
  upper : Nat → Finset V
  tendsto_one : Tendsto (fun n => mu.real
    (D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent
      (rPrimal n) (Rdeep n) (cArm n) (dArm n)
        (width n) (lower n) (upper n))) atTop (nhds 1)
  disjoint_band : ∀ n, Disjoint
    (D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent
      (rPrimal n) (Rdeep n) (cArm n) (dArm n)
        (width n) (lower n) (upper n))
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
        rDual (-(band : Real)) band)



theorem dual_boundaryBand_measure_eq_zero_of_finiteDeepConnector_tendsto_one
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (rPrimal Rdeep cArm dArm : Nat → Real)
    (width : Nat → Nat) (L U : Nat → Finset V)
    (rDual cBand dBand : Real)
    (hdeep : Tendsto (fun n => mu.real
      (D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent
        (rPrimal n) (Rdeep n) (cArm n) (dArm n)
          (width n) (L n) (U n))) atTop (nhds 1))
    (hdisjoint : ∀ n, Disjoint
      (D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent
        (rPrimal n) (Rdeep n) (cArm n) (dArm n)
          (width n) (L n) (U n))
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
          rDual cBand dBand)) :
    D.dualMeasure mu
      (D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
        rDual cBand dBand) = 0 := by
  let band := D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
    rDual cBand dBand
  let pulled := (dualConfigEquiv D.edgeDual) ⁻¹' band
  have hbandMeas : MeasurableSet band :=
    D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster_measurableSet
      rDual cBand dBand
  have hpulledMeas : MeasurableSet pulled :=
    (continuous_dualConfigEquiv D.edgeDual).measurable hbandMeas
  let barriers : Nat → Set (ConfigSpace (Sym2 V)) := fun n =>
    D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent
      (rPrimal n) (Rdeep n) (cArm n) (dArm n)
        (width n) (L n) (U n)
  have hpulledZero : mu pulled = 0 :=
    measure_eq_zero_of_disjoint_measureReal_tendsto_one
      mu barriers pulled hpulledMeas hdisjoint hdeep
  change Measure.map (dualConfigEquiv D.edgeDual) mu band = 0
  rw [Measure.map_apply
    (continuous_dualConfigEquiv D.edgeDual).measurable hbandMeas]
  exact hpulledZero



theorem complementaryDual_rightHalfPlane_measure_eq_zero_of_finiteDeepConnector_schedules
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hdualErgodic : Pdual.IsErgodic (D.dualMeasure mu))
    (hdualUnique : D.dualMeasure mu
      {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (rDual : Real)
    (hschedule : ∀ band : Nat,
      D.FiniteDeepConnectorBandSchedule mu rDual band) :
    D.dualMeasure mu
      (D.dualEmbedding.rightHalfPlaneHasInfiniteCluster rDual) = 0 := by
  let muDual := D.dualMeasure mu
  letI : IsProbabilityMeasure muDual := by
    dsimp only [muDual, PeriodicPlanarDualPair.dualMeasure]
    exact Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  rcases D.dualEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq_zero_or_one
      muDual hdualErgodic rDual with hzero | hone
  · exact hzero
  · have hboundaryOne :=
      D.dualEmbedding.rightHalfPlaneBoundaryHasInfiniteCluster_measure_eq_one
        muDual hdualErgodic.1 hdualUnique rDual hone
    obtain ⟨band, hbandPos⟩ :=
      D.dualEmbedding.exists_positive_boundaryBandHasInfiniteCluster
        muDual rDual hboundaryOne
    let schedule := hschedule band
    have hbandZero :=
      D.dual_boundaryBand_measure_eq_zero_of_finiteDeepConnector_tendsto_one
        mu schedule.rPrimal schedule.Rdeep schedule.cArm schedule.dArm
          schedule.width schedule.lower schedule.upper rDual
          (-(band : Real)) band schedule.tendsto_one schedule.disjoint_band
    have hbandRealZero : muDual.real
        (D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
          rDual (-(band : Real)) band) = 0 := by
      rw [Measure.real, hbandZero]
      norm_num
    rw [hbandRealZero] at hbandPos
    exact (lt_irrefl 0 hbandPos).elim

end PeriodicPlanarDualPair

end StatMech.FK.PeriodicPlanar

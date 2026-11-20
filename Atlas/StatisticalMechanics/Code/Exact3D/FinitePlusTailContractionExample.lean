/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.AnalyticBridgeTarget
import Code.Exact3D.FinitePlusTailBlockRG
import Code.Exact3D.FinitePlusTailClosedBallRG
import Code.Exact3D.InfiniteTailGeneratedTablePackageExample
import Code.Exact3D.InfiniteTailTableClosedBallRGPackage
import Code.Exact3D.InfiniteTailStableKeyPackageExample









namespace StatMech
namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample
open InfiniteTailGeneratedTablePackageExample
open InfiniteTailTableClosedBallRGPackage



noncomputable def halfThirdScalingCertificate :
    FinitePlusTailLipschitzCertificate 1 ℕ :=
  FinitePlusTailLipschitzCertificate.decoupledScaling
    (n := 1) (α := ℕ)
    ((1 : ℝ) / 2) ((1 : ℝ) / 3) ((1 : ℝ) / 2)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)


theorem halfThirdScalingCertificate_c_eq :
    halfThirdScalingCertificate.c = (1 : ℝ) / 2 := by
  rfl


theorem halfThirdScalingCertificate_mixed_lipschitz
    (x y : FinitePlusTailState 1 ℕ) :
    (halfThirdScalingCertificate.map x).dist
        (halfThirdScalingCertificate.map y) ≤
      ((1 : ℝ) / 2) * x.dist y := by
  simpa [halfThirdScalingCertificate_c_eq] using
    halfThirdScalingCertificate.mixed_lipschitz x y


theorem halfThirdScalingCertificate_c_lt_one :
    halfThirdScalingCertificate.c < 1 := by
  simpa [halfThirdScalingCertificate_c_eq] using
    halfThirdScalingCertificate.c_lt_one


noncomputable def halfThirdScalingBlockBounds :
    FinitePlusTailBlockBounds 1 ℕ :=
  FinitePlusTailBlockBounds.decoupledScaling
    (n := 1) (α := ℕ) ((1 : ℝ) / 2) ((1 : ℝ) / 3)


theorem halfThirdScalingBlockBounds_finite_column :
    halfThirdScalingBlockBounds.finiteToFinite +
        halfThirdScalingBlockBounds.finiteToTail ≤ (1 : ℝ) / 2 := by
  norm_num [halfThirdScalingBlockBounds,
    FinitePlusTailBlockBounds.decoupledScaling,
    FinitePlusTailBlockBounds.ofDecoupled]



theorem halfThirdScalingBlockBounds_tail_column :
    halfThirdScalingBlockBounds.tailToFinite +
        halfThirdScalingBlockBounds.tailToTail ≤ (1 : ℝ) / 2 := by
  norm_num [halfThirdScalingBlockBounds,
    FinitePlusTailBlockBounds.decoupledScaling,
    FinitePlusTailBlockBounds.ofDecoupled]



noncomputable def halfThirdScalingFromBlockBoundsCertificate :
    FinitePlusTailLipschitzCertificate 1 ℕ :=
  halfThirdScalingBlockBounds.toLipschitzCertificate
    (c := (1 : ℝ) / 2)
    (by norm_num)
    (by norm_num)
    halfThirdScalingBlockBounds_finite_column
    halfThirdScalingBlockBounds_tail_column


theorem halfThirdScalingFromBlockBoundsCertificate_c_eq :
    halfThirdScalingFromBlockBoundsCertificate.c = (1 : ℝ) / 2 := by
  rfl


theorem halfThirdScalingBlockBounds_mixed_lipschitz
    (x y : FinitePlusTailState 1 ℕ) :
    (halfThirdScalingBlockBounds.map x).dist
        (halfThirdScalingBlockBounds.map y) ≤
      ((1 : ℝ) / 2) * x.dist y := by
  exact halfThirdScalingBlockBounds.mixed_lipschitz
    (c := (1 : ℝ) / 2) (by norm_num) (by norm_num)
    halfThirdScalingBlockBounds_finite_column
    halfThirdScalingBlockBounds_tail_column x y


noncomputable def zeroState : FinitePlusTailState 1 ℕ where
  finite := 0
  tail := 0


theorem zeroState_eq_ofFinite :
    zeroState =
      FinitePlusTailState.ofFinite (α := ℕ) (0 : Fin 1 → ℝ) :=
  rfl



noncomputable def zeroFiniteClosedBallCertificate {radius : ℝ}
    (hradius : 0 ≤ radius) :
    FiniteContraction.ClosedBallContractionCertificate
      (@FiniteContraction.zeroMap 1) :=
  FiniteContraction.zeroMap_closedBallContractionCertificate
    (n := 1) hradius


noncomputable def zeroFiniteClosedBallLift {radius : ℝ}
    (hradius : 0 ≤ radius) :
    FinitePlusTailClosedBallContractionCertificate 1 ℕ :=
  FinitePlusTailClosedBallContractionCertificate.ofFiniteClosedBall
    (α := ℕ) (zeroFiniteClosedBallCertificate hradius)



theorem zeroFiniteClosedBallLift_center_eq {radius : ℝ}
    (hradius : 0 ≤ radius) :
    (zeroFiniteClosedBallLift hradius).center = zeroState := by
  rfl


theorem zeroFiniteClosedBallLift_exists_fixedPoint {radius : ℝ}
    (hradius : 0 ≤ radius) :
    ∃ p : FinitePlusTailState 1 ℕ,
      (zeroFiniteClosedBallLift hradius).contraction.map p = p ∧
        FinitePlusTailState.ClosedBall zeroState radius p := by
  simpa [zeroFiniteClosedBallLift_center_eq hradius] using
    (zeroFiniteClosedBallLift hradius).exists_fixedPoint



noncomputable def unitCenterState : FinitePlusTailState 1 ℕ where
  finite := fun _ => 1
  tail := 0


theorem halfThirdScalingCertificate_map_zero :
    halfThirdScalingCertificate.map zeroState = zeroState := by
  ext i <;>
    simp [zeroState, halfThirdScalingCertificate,
      FinitePlusTailLipschitzCertificate.decoupledScaling,
      FinitePlusTailLipschitzCertificate.ofDecoupled,
      SummableTail.scale]


theorem halfThirdScalingCertificate_map_origin :
    halfThirdScalingCertificate.map
        (FinitePlusTailState.origin : FinitePlusTailState 1 ℕ) =
      FinitePlusTailState.origin := by
  simpa [zeroState, FinitePlusTailState.origin] using
    halfThirdScalingCertificate_map_zero


theorem halfThirdScalingBlockBounds_map_zero :
    halfThirdScalingBlockBounds.map zeroState = zeroState := by
  ext i <;>
    simp [zeroState, halfThirdScalingBlockBounds,
      FinitePlusTailBlockBounds.map,
      FinitePlusTailBlockBounds.decoupledScaling,
      FinitePlusTailBlockBounds.ofDecoupled,
      SummableTail.scale]


theorem halfThirdScalingBlockBounds_map_origin :
    halfThirdScalingBlockBounds.map
        (FinitePlusTailState.origin : FinitePlusTailState 1 ℕ) =
      FinitePlusTailState.origin := by
  simpa [zeroState, FinitePlusTailState.origin] using
    halfThirdScalingBlockBounds_map_zero


theorem halfThirdScalingBlockBounds_zero_residual :
    (halfThirdScalingBlockBounds.map zeroState).dist zeroState ≤ 0 := by
  rw [halfThirdScalingBlockBounds_map_zero, FinitePlusTailState.dist_self]


theorem halfThirdScalingBlockBounds_zero_finiteResidual :
    FiniteContraction.l1Dist
      (halfThirdScalingBlockBounds.finiteMap zeroState) zeroState.finite ≤ 0 := by
  norm_num [halfThirdScalingBlockBounds,
    FinitePlusTailBlockBounds.decoupledScaling,
    FinitePlusTailBlockBounds.ofDecoupled,
    zeroState, FiniteContraction.l1Dist, RatInterval.supNormVec]


theorem halfThirdScalingBlockBounds_zero_tailResidual :
    (halfThirdScalingBlockBounds.tailMap zeroState).dist zeroState.tail ≤ 0 := by
  simp [halfThirdScalingBlockBounds,
    FinitePlusTailBlockBounds.decoupledScaling,
    FinitePlusTailBlockBounds.ofDecoupled,
    zeroState, SummableTail.scale, SummableTail.dist]



def halfThirdScalingBlockBoundsZeroFiniteResidual :
    RatInterval.IntervalVector 1 :=
  RatInterval.pointVector (fun _ => 0)



theorem halfThirdScalingBlockBounds_zero_finiteResidual_mem :
    RatInterval.VectorMem
      (fun i =>
        halfThirdScalingBlockBounds.finiteMap zeroState i -
          zeroState.finite i)
      halfThirdScalingBlockBoundsZeroFiniteResidual := by
  intro i
  fin_cases i
  norm_num [halfThirdScalingBlockBoundsZeroFiniteResidual,
    halfThirdScalingBlockBounds,
    FinitePlusTailBlockBounds.decoupledScaling,
    FinitePlusTailBlockBounds.ofDecoupled,
    zeroState, RatInterval.pointVector, RatInterval.point,
    RatInterval.MemR]


theorem halfThirdScalingBlockBounds_zero_finiteResidual_absSum :
    RatInterval.VectorAbsSum
      halfThirdScalingBlockBoundsZeroFiniteResidual = 0 := by
  norm_num [halfThirdScalingBlockBoundsZeroFiniteResidual,
    RatInterval.VectorAbsSum_pointVector]


noncomputable def halfThirdScalingBlockBoundsComponentClosedBallCertificate
    {radius : ℝ} (hradius : 0 ≤ radius) :
    FinitePlusTailClosedBallContractionCertificate 1 ℕ :=
  halfThirdScalingBlockBounds.toClosedBallCertificateOfComponentResiduals
    (c := (1 : ℝ) / 2)
    (by norm_num)
    (by norm_num)
    halfThirdScalingBlockBounds_finite_column
    halfThirdScalingBlockBounds_tail_column
    zeroState
    hradius
    halfThirdScalingBlockBounds_zero_finiteResidual
    halfThirdScalingBlockBounds_zero_tailResidual
    (by nlinarith)



noncomputable def halfThirdScalingBlockBoundsFiniteResidualVectorClosedBallCertificate
    {radius : ℝ} (hradius : 0 ≤ radius) :
    FinitePlusTailClosedBallContractionCertificate 1 ℕ :=
  halfThirdScalingBlockBounds.toClosedBallCertificateOfFiniteResidualVector
    (c := (1 : ℝ) / 2)
    (by norm_num)
    (by norm_num)
    halfThirdScalingBlockBounds_finite_column
    halfThirdScalingBlockBounds_tail_column
    zeroState
    hradius
    halfThirdScalingBlockBounds_zero_finiteResidual_mem
    halfThirdScalingBlockBounds_zero_tailResidual
    (by
      rw [halfThirdScalingBlockBounds_zero_finiteResidual_absSum]
      nlinarith)



theorem halfThirdScalingBlockBoundsComponentClosedBallCertificate_exists_fixedPoint
    {radius : ℝ} (hradius : 0 ≤ radius) :
    ∃ p : FinitePlusTailState 1 ℕ,
      halfThirdScalingBlockBounds.map p = p ∧
        FinitePlusTailState.ClosedBall zeroState radius p := by
  simpa [halfThirdScalingBlockBoundsComponentClosedBallCertificate,
    FinitePlusTailClosedBallContractionCertificate.fixedPoint] using
    (halfThirdScalingBlockBoundsComponentClosedBallCertificate
      hradius).exists_fixedPoint



theorem halfThirdScalingBlockBoundsComponentClosedBallCertificate_fixedPoint_isFixed
    {radius : ℝ} (hradius : 0 ≤ radius) :
    halfThirdScalingBlockBounds.map
      (halfThirdScalingBlockBoundsComponentClosedBallCertificate
        hradius).fixedPoint =
      (halfThirdScalingBlockBoundsComponentClosedBallCertificate
        hradius).fixedPoint := by
  simpa [halfThirdScalingBlockBoundsComponentClosedBallCertificate] using
    FinitePlusTailBlockBounds.toClosedBallCertificateOfComponentResiduals_fixedPoint_isFixed
      halfThirdScalingBlockBounds
      (c := (1 : ℝ) / 2)
      (by norm_num)
      (by norm_num)
      halfThirdScalingBlockBounds_finite_column
      halfThirdScalingBlockBounds_tail_column
      zeroState
      hradius
      halfThirdScalingBlockBounds_zero_finiteResidual
      halfThirdScalingBlockBounds_zero_tailResidual
      (by nlinarith)



theorem halfThirdScalingBlockBoundsFiniteResidualVectorClosedBallCertificate_fixedPoint_isFixed
    {radius : ℝ} (hradius : 0 ≤ radius) :
    halfThirdScalingBlockBounds.map
      (halfThirdScalingBlockBoundsFiniteResidualVectorClosedBallCertificate
        hradius).fixedPoint =
      (halfThirdScalingBlockBoundsFiniteResidualVectorClosedBallCertificate
        hradius).fixedPoint := by
  simpa [halfThirdScalingBlockBoundsFiniteResidualVectorClosedBallCertificate] using
    FinitePlusTailBlockBounds.toClosedBallCertificateOfFiniteResidualVector_fixedPoint_isFixed
      halfThirdScalingBlockBounds
      (c := (1 : ℝ) / 2)
      (by norm_num)
      (by norm_num)
      halfThirdScalingBlockBounds_finite_column
      halfThirdScalingBlockBounds_tail_column
      zeroState
      hradius
      halfThirdScalingBlockBounds_zero_finiteResidual_mem
      halfThirdScalingBlockBounds_zero_tailResidual
      (by
        rw [halfThirdScalingBlockBounds_zero_finiteResidual_absSum]
        nlinarith)




theorem halfThirdScalingCertificate_iterate_mem_thermalStableCone
    {thermal η t : ℝ} {s : FinitePlusTailState 1 ℕ}
    (hη : 0 ≤ η)
    (hdom : ((1 : ℝ) / 2) ≤ |thermal|)
    (hs : FinitePlusTailState.ThermalStableCone η t s)
    (k : ℕ) :
    FinitePlusTailState.ThermalStableCone η (thermal ^ k * t)
      (halfThirdScalingCertificate.iterate k s) :=
  halfThirdScalingCertificate.iterate_mem_thermalStableCone_of_c_le_abs_thermal
    halfThirdScalingCertificate_map_origin hη
    (by simpa [halfThirdScalingCertificate_c_eq] using hdom) hs k



noncomputable def halfThirdScalingHyperbolicSplitting :
    FinitePlusTailHyperbolicSplitting 1 ℕ where
  thermal := 3
  thermal_gt_one := by norm_num
  stable := halfThirdScalingCertificate
  stable_origin := halfThirdScalingCertificate_map_origin
  stable_dominated := by
    rw [halfThirdScalingCertificate_c_eq]
    norm_num



theorem halfThirdScalingHyperbolicSplitting_cone_iterate
    {η : ℝ} (hη : 0 ≤ η)
    {x : FinitePlusTailHyperbolicSplitting.State 1 ℕ}
    (hx : halfThirdScalingHyperbolicSplitting.cone η x)
    (k : ℕ) :
    halfThirdScalingHyperbolicSplitting.cone η
      (halfThirdScalingHyperbolicSplitting.iterate k x) :=
  halfThirdScalingHyperbolicSplitting.cone_iterate hη hx k


def halfThirdScalingBlockScale : BlockScale where
  L := 2
  one_lt := by norm_num



noncomputable def halfThirdScalingModel : CriticalModel Unit where
  betaC := 0
  twoPoint := fun _ _ _ => 0



noncomputable def halfThirdScalingRGCertificate :
    RGCertificate halfThirdScalingModel :=
  halfThirdScalingHyperbolicSplitting.certificate
    halfThirdScalingBlockScale halfThirdScalingModel



theorem halfThirdScalingRGCertificate_fixedPointEnclosure :
    halfThirdScalingRGCertificate.FixedPointEnclosure := by
  simpa [halfThirdScalingRGCertificate] using
    halfThirdScalingHyperbolicSplitting.certificate_fixedPointEnclosure
      halfThirdScalingBlockScale halfThirdScalingModel



theorem halfThirdScalingRGCertificate_hyperbolicSplitting :
    halfThirdScalingRGCertificate.HyperbolicSplitting :=
  halfThirdScalingRGCertificate.hyperbolicSplitting_of_thermal_gt_one



theorem halfThirdScalingRGCertificate_linearizationEnclosure :
    halfThirdScalingRGCertificate.LinearizationEnclosure :=
  halfThirdScalingRGCertificate.linearizationEnclosure_of_thermal_gt_one



theorem halfThirdScalingRGCertificate_predictedExponent_eq :
    halfThirdScalingRGCertificate.predictedExponent =
      predictedNu halfThirdScalingBlockScale 3 :=
  rfl



theorem halfThirdScalingRGCertificate_cone_iterate
    {η : ℝ} (hη : 0 ≤ η)
    {x : halfThirdScalingRGCertificate.H.carrier}
    (hx : halfThirdScalingHyperbolicSplitting.cone η x)
    (k : ℕ) :
    halfThirdScalingHyperbolicSplitting.cone η
      (((halfThirdScalingRGCertificate.R.map)^[k]) x) := by
  simpa [halfThirdScalingRGCertificate] using
    halfThirdScalingHyperbolicSplitting.certificate_cone_iterate
      halfThirdScalingBlockScale halfThirdScalingModel hη hx k



theorem halfThirdScalingRGCertificate_valid_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      halfThirdScalingRGCertificate.RGToExponentBridge correlationLength) :
    halfThirdScalingRGCertificate.Valid correlationLength := by
  simpa [halfThirdScalingRGCertificate] using
    halfThirdScalingHyperbolicSplitting.certificate_valid_of_bridge
      halfThirdScalingBlockScale halfThirdScalingModel correlationLength hbridge



theorem halfThirdScalingRGCertificate_hasCriticalNu_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      halfThirdScalingRGCertificate.RGToExponentBridge correlationLength) :
    HasCriticalNu halfThirdScalingModel correlationLength
      halfThirdScalingRGCertificate.predictedExponent :=
  (halfThirdScalingRGCertificate_valid_of_bridge
    correlationLength hbridge).hasCriticalNu



theorem halfThirdScalingRGCertificate_rgToExponentBridge_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu halfThirdScalingModel correlationLength
        halfThirdScalingRGCertificate.predictedExponent) :
    halfThirdScalingRGCertificate.RGToExponentBridge correlationLength := by
  simpa [halfThirdScalingRGCertificate] using
    halfThirdScalingHyperbolicSplitting.certificate_rgToExponentBridge_of_hasCriticalNu
      halfThirdScalingBlockScale halfThirdScalingModel correlationLength hν



theorem halfThirdScalingRGCertificate_valid_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu halfThirdScalingModel correlationLength
        halfThirdScalingRGCertificate.predictedExponent) :
    halfThirdScalingRGCertificate.Valid correlationLength := by
  simpa [halfThirdScalingRGCertificate] using
    halfThirdScalingHyperbolicSplitting.certificate_valid_of_hasCriticalNu
      halfThirdScalingBlockScale halfThirdScalingModel correlationLength hν



noncomputable def halfThirdScalingCorrelationLength (β : ℝ) : ℝ :=
  Real.exp
    (-halfThirdScalingRGCertificate.predictedExponent *
      Real.log (halfThirdScalingModel.betaC - β))


theorem halfThirdScalingCorrelationLength_pos :
    ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC),
      0 < halfThirdScalingCorrelationLength β :=
  Filter.Eventually.of_forall fun _ => by
    exact Real.exp_pos _



theorem halfThirdScalingCorrelationLength_exact_power :
    ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC),
      halfThirdScalingCorrelationLength β =
        Real.exp
          (-halfThirdScalingRGCertificate.predictedExponent *
            Real.log (halfThirdScalingModel.betaC - β)) :=
  Filter.Eventually.of_forall fun _ => rfl




def halfThirdScalingToyRGCovariance : Prop :=
  True


def halfThirdScalingToyStableManifoldControl : Prop :=
  True


def halfThirdScalingToyMicroscopicOrbitEntry : Prop :=
  True


def halfThirdScalingToySubcriticalMassBridge : Prop :=
  True

theorem halfThirdScalingToyRGCovariance_proof :
    halfThirdScalingToyRGCovariance := by
  trivial

theorem halfThirdScalingToyStableManifoldControl_proof :
    halfThirdScalingToyStableManifoldControl := by
  trivial

theorem halfThirdScalingToyMicroscopicOrbitEntry_proof :
    halfThirdScalingToyMicroscopicOrbitEntry := by
  trivial

theorem halfThirdScalingToySubcriticalMassBridge_proof :
    halfThirdScalingToySubcriticalMassBridge := by
  trivial



noncomputable def halfThirdScalingAnalyticBridgeInputs :
    RGCertificate.AnalyticBridgeInputs halfThirdScalingRGCertificate
      halfThirdScalingCorrelationLength
      halfThirdScalingToyRGCovariance
      halfThirdScalingToyStableManifoldControl
      halfThirdScalingToyMicroscopicOrbitEntry
      halfThirdScalingToySubcriticalMassBridge :=
  RGCertificate.AnalyticBridgeInputs.of_eventually_exact_power_with_inputs
    halfThirdScalingToyRGCovariance_proof
    halfThirdScalingToyStableManifoldControl_proof
    halfThirdScalingToyMicroscopicOrbitEntry_proof
    halfThirdScalingToySubcriticalMassBridge_proof
    halfThirdScalingCorrelationLength_exact_power


theorem halfThirdScalingRGCertificate_bridge_from_analyticInputs :
    halfThirdScalingRGCertificate.RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  RGCertificate.AnalyticBridgeInputs.rgToExponentBridge
    halfThirdScalingAnalyticBridgeInputs



theorem halfThirdScalingRGCertificate_valid_from_analyticInputs :
    halfThirdScalingRGCertificate.Valid halfThirdScalingCorrelationLength :=
  RGCertificate.AnalyticBridgeInputs.valid_of_checks
    halfThirdScalingAnalyticBridgeInputs
    trivial trivial halfThirdScalingRGCertificate_fixedPointEnclosure
    halfThirdScalingRGCertificate_linearizationEnclosure
    halfThirdScalingRGCertificate_hyperbolicSplitting trivial


theorem halfThirdScalingRGCertificate_hasCriticalNu_from_analyticInputs :
    HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength
      halfThirdScalingRGCertificate.predictedExponent :=
  RGCertificate.AnalyticBridgeInputs.hasCriticalNu
    halfThirdScalingAnalyticBridgeInputs


noncomputable def halfThirdScalingPrefactor (_β : ℝ) : ℝ :=
  1



noncomputable def halfThirdScalingDoublePrefactor (_β : ℝ) : ℝ :=
  2


theorem halfThirdScalingPrefactor_pos :
    ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC),
      0 < halfThirdScalingPrefactor β :=
  Filter.Eventually.of_forall fun _ => by
    norm_num [halfThirdScalingPrefactor]


theorem halfThirdScalingPrefactor_log_negligible :
    Filter.Tendsto
      (fun β : ℝ =>
        Real.log (halfThirdScalingPrefactor β) /
          Real.log (halfThirdScalingModel.betaC - β))
      (nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC)) (nhds 0) := by
  simp [halfThirdScalingPrefactor]


theorem halfThirdScalingDoublePrefactor_pos :
    ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC),
      0 < halfThirdScalingDoublePrefactor β :=
  Filter.Eventually.of_forall fun _ => by
    norm_num [halfThirdScalingDoublePrefactor]


theorem halfThirdScalingDoublePrefactor_log_negligible :
    Filter.Tendsto
      (fun β : ℝ =>
        Real.log (halfThirdScalingDoublePrefactor β) /
          Real.log (halfThirdScalingModel.betaC - β))
      (nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC)) (nhds 0) := by
  let L := nhdsWithin halfThirdScalingModel.betaC
    (Set.Iio halfThirdScalingModel.betaC)
  have hlogd :
      Filter.Tendsto
        (fun β : ℝ => Real.log (halfThirdScalingModel.betaC - β))
        L Filter.atBot := by
    simpa [L] using tendsto_log_betaC_sub_atBot halfThirdScalingModel
  simpa [halfThirdScalingDoublePrefactor, L] using
    hlogd.const_div_atBot (Real.log (2 : ℝ))


theorem halfThirdScalingCorrelationLength_prefactor_power :
    ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC),
      halfThirdScalingCorrelationLength β =
        halfThirdScalingPrefactor β *
          Real.exp
            (-halfThirdScalingRGCertificate.predictedExponent *
              Real.log (halfThirdScalingModel.betaC - β)) :=
  Filter.Eventually.of_forall fun _ => by
    simp [halfThirdScalingCorrelationLength, halfThirdScalingPrefactor]



noncomputable def halfThirdScalingAnalyticPrefactorBridgeInputs :
    RGCertificate.AnalyticPrefactorBridgeInputs
      halfThirdScalingRGCertificate halfThirdScalingCorrelationLength
      halfThirdScalingPrefactor
      halfThirdScalingToyRGCovariance
      halfThirdScalingToyStableManifoldControl
      halfThirdScalingToyMicroscopicOrbitEntry
      halfThirdScalingToySubcriticalMassBridge :=
  RGCertificate.AnalyticPrefactorBridgeInputs.of_eventually_prefactor_power_with_inputs
    halfThirdScalingToyRGCovariance_proof
    halfThirdScalingToyStableManifoldControl_proof
    halfThirdScalingToyMicroscopicOrbitEntry_proof
    halfThirdScalingToySubcriticalMassBridge_proof
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    halfThirdScalingCorrelationLength_prefactor_power


theorem halfThirdScalingRGCertificate_bridge_from_prefactorInputs :
    halfThirdScalingRGCertificate.RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  RGCertificate.AnalyticPrefactorBridgeInputs.rgToExponentBridge
    halfThirdScalingAnalyticPrefactorBridgeInputs



theorem halfThirdScalingRGCertificate_valid_from_prefactorInputs :
    halfThirdScalingRGCertificate.Valid halfThirdScalingCorrelationLength :=
  RGCertificate.AnalyticPrefactorBridgeInputs.valid_of_checks
    halfThirdScalingAnalyticPrefactorBridgeInputs
    trivial trivial halfThirdScalingRGCertificate_fixedPointEnclosure
    halfThirdScalingRGCertificate_linearizationEnclosure
    halfThirdScalingRGCertificate_hyperbolicSplitting trivial



theorem halfThirdScalingRGCertificate_valid_from_powerLawWrapper :
    halfThirdScalingRGCertificate.Valid halfThirdScalingCorrelationLength :=
  halfThirdScalingRGCertificate.valid_of_eventually_exact_power_variable_prefactor
    halfThirdScalingCorrelationLength halfThirdScalingPrefactor
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    halfThirdScalingCorrelationLength_prefactor_power
    trivial trivial halfThirdScalingRGCertificate_fixedPointEnclosure
    halfThirdScalingRGCertificate_linearizationEnclosure
    halfThirdScalingRGCertificate_hyperbolicSplitting trivial



theorem halfThirdScalingRGCertificate_hasCriticalNu_from_powerLawWrapper :
    HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength
      halfThirdScalingRGCertificate.predictedExponent :=
  halfThirdScalingRGCertificate_valid_from_powerLawWrapper.hasCriticalNu



theorem halfThirdScalingRGCertificate_valid_from_prefactorTransport :
    halfThirdScalingRGCertificate.Valid
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  RGCertificate.Valid.mul_log_negligible_prefactor
    halfThirdScalingRGCertificate_valid_from_powerLawWrapper
    halfThirdScalingCorrelationLength_pos
    halfThirdScalingDoublePrefactor_pos
    halfThirdScalingDoublePrefactor_log_negligible



theorem halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorTransport :
    HasCriticalNu halfThirdScalingModel
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β)
      halfThirdScalingRGCertificate.predictedExponent :=
  halfThirdScalingRGCertificate_valid_from_prefactorTransport.hasCriticalNu



theorem halfThirdScalingDoubleComparison :
    ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC),
      (2 : ℝ) * halfThirdScalingCorrelationLength β ≤
          halfThirdScalingDoublePrefactor β *
            halfThirdScalingCorrelationLength β ∧
        halfThirdScalingDoublePrefactor β *
            halfThirdScalingCorrelationLength β ≤
          (2 : ℝ) * halfThirdScalingCorrelationLength β :=
  Filter.Eventually.of_forall fun β => by
    simp [halfThirdScalingDoublePrefactor]



theorem halfThirdScalingRGCertificate_valid_from_constantComparison :
    halfThirdScalingRGCertificate.Valid
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  RGCertificate.Valid.of_eventually_const_mul_le_le
    halfThirdScalingRGCertificate_valid_from_powerLawWrapper
    halfThirdScalingCorrelationLength_pos
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)
    halfThirdScalingDoubleComparison



theorem halfThirdScalingRGCertificate_hasCriticalNu_from_constantComparison :
    HasCriticalNu halfThirdScalingModel
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β)
      halfThirdScalingRGCertificate.predictedExponent :=
  halfThirdScalingRGCertificate_valid_from_constantComparison.hasCriticalNu


theorem halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs :
    HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength
      halfThirdScalingRGCertificate.predictedExponent :=
  RGCertificate.AnalyticPrefactorBridgeInputs.hasCriticalNu
    halfThirdScalingAnalyticPrefactorBridgeInputs


noncomputable def halfThirdScalingMass (β : ℝ) : ℝ :=
  Real.exp
    (halfThirdScalingRGCertificate.predictedExponent *
      Real.log (halfThirdScalingModel.betaC - β))


noncomputable def halfThirdScalingMassPrefactor (_β : ℝ) : ℝ :=
  1


theorem halfThirdScalingMassPrefactor_pos :
    ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC),
      0 < halfThirdScalingMassPrefactor β :=
  Filter.Eventually.of_forall fun _ => by
    norm_num [halfThirdScalingMassPrefactor]


theorem halfThirdScalingMassPrefactor_log_negligible :
    Filter.Tendsto
      (fun β : ℝ =>
        Real.log (halfThirdScalingMassPrefactor β) /
          Real.log (halfThirdScalingModel.betaC - β))
      (nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC)) (nhds 0) := by
  simp [halfThirdScalingMassPrefactor]



theorem halfThirdScalingMass_power :
    ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC),
      halfThirdScalingMass β =
        halfThirdScalingMassPrefactor β *
          Real.exp
            (halfThirdScalingRGCertificate.predictedExponent *
              Real.log (halfThirdScalingModel.betaC - β)) :=
  Filter.Eventually.of_forall fun _ => by
    simp [halfThirdScalingMass, halfThirdScalingMassPrefactor]


theorem halfThirdScalingCorrelationLength_eq_inv_mass :
    ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC),
      halfThirdScalingCorrelationLength β = (halfThirdScalingMass β)⁻¹ :=
  Filter.Eventually.of_forall fun β => by
    unfold halfThirdScalingCorrelationLength halfThirdScalingMass
    rw [show
        -halfThirdScalingRGCertificate.predictedExponent *
            Real.log (halfThirdScalingModel.betaC - β) =
          -(halfThirdScalingRGCertificate.predictedExponent *
            Real.log (halfThirdScalingModel.betaC - β)) by
        ring,
      Real.exp_neg]



noncomputable def halfThirdScalingAnalyticMassBridgeInputs :
    RGCertificate.AnalyticMassBridgeInputs
      halfThirdScalingRGCertificate halfThirdScalingCorrelationLength
      halfThirdScalingMass halfThirdScalingMassPrefactor
      halfThirdScalingToyRGCovariance
      halfThirdScalingToyStableManifoldControl
      halfThirdScalingToyMicroscopicOrbitEntry
      halfThirdScalingToySubcriticalMassBridge :=
  RGCertificate.AnalyticMassBridgeInputs.of_eventually_mass_power_with_inputs
    halfThirdScalingToyRGCovariance_proof
    halfThirdScalingToyStableManifoldControl_proof
    halfThirdScalingToyMicroscopicOrbitEntry_proof
    halfThirdScalingToySubcriticalMassBridge_proof
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    halfThirdScalingMass_power
    halfThirdScalingCorrelationLength_eq_inv_mass


theorem halfThirdScalingRGCertificate_bridge_from_massInputs :
    halfThirdScalingRGCertificate.RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  RGCertificate.AnalyticMassBridgeInputs.rgToExponentBridge
    halfThirdScalingAnalyticMassBridgeInputs



theorem halfThirdScalingRGCertificate_valid_from_massInputs :
    halfThirdScalingRGCertificate.Valid halfThirdScalingCorrelationLength :=
  RGCertificate.AnalyticMassBridgeInputs.valid_of_checks
    halfThirdScalingAnalyticMassBridgeInputs
    trivial trivial halfThirdScalingRGCertificate_fixedPointEnclosure
    halfThirdScalingRGCertificate_linearizationEnclosure
    halfThirdScalingRGCertificate_hyperbolicSplitting trivial



theorem halfThirdScalingRGCertificate_valid_from_massPowerLawWrapper :
    halfThirdScalingRGCertificate.Valid halfThirdScalingCorrelationLength :=
  halfThirdScalingRGCertificate.valid_of_eventually_exact_mass_power_variable_prefactor
    halfThirdScalingCorrelationLength halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    halfThirdScalingMass_power
    halfThirdScalingCorrelationLength_eq_inv_mass
    trivial trivial halfThirdScalingRGCertificate_fixedPointEnclosure
    halfThirdScalingRGCertificate_linearizationEnclosure
    halfThirdScalingRGCertificate_hyperbolicSplitting trivial



theorem halfThirdScalingRGCertificate_hasCriticalNu_from_massPowerLawWrapper :
    HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength
      halfThirdScalingRGCertificate.predictedExponent :=
  halfThirdScalingRGCertificate_valid_from_massPowerLawWrapper.hasCriticalNu


theorem halfThirdScalingRGCertificate_hasCriticalNu_from_massInputs :
    HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength
      halfThirdScalingRGCertificate.predictedExponent :=
  RGCertificate.AnalyticMassBridgeInputs.hasCriticalNu
    halfThirdScalingAnalyticMassBridgeInputs



noncomputable def halfThirdScalingBlockRGPackage :
    FinitePlusTailBlockRGPackage 1 ℕ where
  blockBounds := halfThirdScalingBlockBounds
  c := (1 : ℝ) / 2
  c_nonneg := by norm_num
  c_lt_one := by norm_num
  finite_column_sum_le := halfThirdScalingBlockBounds_finite_column
  tail_column_sum_le := halfThirdScalingBlockBounds_tail_column
  origin_fixed := halfThirdScalingBlockBounds_map_origin
  thermal := 3
  thermal_gt_one := by norm_num
  stable_dominated := by norm_num



theorem halfThirdScalingBlockRGPackage_predictedExponent_eq :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent =
        predictedNu halfThirdScalingBlockScale 3 :=
  halfThirdScalingBlockRGPackage.certificate_predictedExponent_eq
    halfThirdScalingBlockScale halfThirdScalingModel


noncomputable def halfThirdScalingBlockRGPackage_relaxedC :
    FinitePlusTailBlockRGPackage 1 ℕ :=
  halfThirdScalingBlockRGPackage.with_larger_c
    (c' := (3 : ℝ) / 4)
    (by norm_num [halfThirdScalingBlockRGPackage])
    (by norm_num)
    (by norm_num [halfThirdScalingBlockRGPackage])


theorem halfThirdScalingBlockRGPackage_relaxedC_c :
    halfThirdScalingBlockRGPackage_relaxedC.c = (3 : ℝ) / 4 :=
  rfl



theorem halfThirdScalingBlockRGPackage_relaxedC_certificate_eq :
    halfThirdScalingBlockRGPackage_relaxedC.certificate
      halfThirdScalingBlockScale halfThirdScalingModel =
        halfThirdScalingBlockRGPackage.certificate
          halfThirdScalingBlockScale halfThirdScalingModel :=
  rfl



theorem halfThirdScalingBlockRGPackage_relaxedC_predictedExponent_eq :
    (halfThirdScalingBlockRGPackage_relaxedC.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent =
        predictedNu halfThirdScalingBlockScale 3 :=
  halfThirdScalingBlockRGPackage_relaxedC.certificate_predictedExponent_eq
    halfThirdScalingBlockScale halfThirdScalingModel



theorem halfThirdScalingBlockRGPackage_relaxedC_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu halfThirdScalingModel correlationLength
        (halfThirdScalingBlockRGPackage.certificate
          halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent) :
    HasCriticalNu halfThirdScalingModel correlationLength
      (halfThirdScalingBlockRGPackage_relaxedC.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  simpa [halfThirdScalingBlockRGPackage_relaxedC] using
    halfThirdScalingBlockRGPackage.with_larger_c_hasCriticalNu
      (c' := (3 : ℝ) / 4)
      (by norm_num [halfThirdScalingBlockRGPackage])
      (by norm_num)
      (by norm_num [halfThirdScalingBlockRGPackage])
      halfThirdScalingBlockScale halfThirdScalingModel hν



noncomputable def halfThirdScalingBlockRGPackage_relaxedConstants :
    FinitePlusTailBlockRGPackage 1 ℕ :=
  halfThirdScalingBlockRGPackage.with_larger_constants
    (finiteToFinite' := (1 : ℝ) / 2)
    (tailToFinite' := 0)
    (finiteToTail' := 0)
    (tailToTail' := (1 : ℝ) / 2)
    (c' := (3 : ℝ) / 4)
    (by
      norm_num [halfThirdScalingBlockRGPackage, halfThirdScalingBlockBounds,
        FinitePlusTailBlockBounds.decoupledScaling,
        FinitePlusTailBlockBounds.ofDecoupled])
    (by
      norm_num [halfThirdScalingBlockRGPackage, halfThirdScalingBlockBounds,
        FinitePlusTailBlockBounds.decoupledScaling,
        FinitePlusTailBlockBounds.ofDecoupled])
    (by
      norm_num [halfThirdScalingBlockRGPackage, halfThirdScalingBlockBounds,
        FinitePlusTailBlockBounds.decoupledScaling,
        FinitePlusTailBlockBounds.ofDecoupled])
    (by
      norm_num [halfThirdScalingBlockRGPackage, halfThirdScalingBlockBounds,
        FinitePlusTailBlockBounds.decoupledScaling,
        FinitePlusTailBlockBounds.ofDecoupled])
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num [halfThirdScalingBlockRGPackage])



theorem halfThirdScalingBlockRGPackage_relaxedConstants_c :
    halfThirdScalingBlockRGPackage_relaxedConstants.c = (3 : ℝ) / 4 :=
  rfl


theorem halfThirdScalingBlockRGPackage_relaxedConstants_certificate_eq :
    halfThirdScalingBlockRGPackage_relaxedConstants.certificate
      halfThirdScalingBlockScale halfThirdScalingModel =
        halfThirdScalingBlockRGPackage.certificate
          halfThirdScalingBlockScale halfThirdScalingModel :=
  rfl



theorem halfThirdScalingBlockRGPackage_relaxedConstants_predictedExponent_eq :
    (halfThirdScalingBlockRGPackage_relaxedConstants.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent =
        predictedNu halfThirdScalingBlockScale 3 :=
  halfThirdScalingBlockRGPackage_relaxedConstants.certificate_predictedExponent_eq
    halfThirdScalingBlockScale halfThirdScalingModel



theorem halfThirdScalingBlockRGPackage_relaxedConstants_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu halfThirdScalingModel correlationLength
        (halfThirdScalingBlockRGPackage.certificate
          halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent) :
    HasCriticalNu halfThirdScalingModel correlationLength
      (halfThirdScalingBlockRGPackage_relaxedConstants.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  simpa [halfThirdScalingBlockRGPackage_relaxedConstants] using
    halfThirdScalingBlockRGPackage.with_larger_constants_hasCriticalNu
      (finiteToFinite' := (1 : ℝ) / 2)
      (tailToFinite' := 0)
      (finiteToTail' := 0)
      (tailToTail' := (1 : ℝ) / 2)
      (c' := (3 : ℝ) / 4)
      (by
        norm_num [halfThirdScalingBlockRGPackage, halfThirdScalingBlockBounds,
          FinitePlusTailBlockBounds.decoupledScaling,
          FinitePlusTailBlockBounds.ofDecoupled])
      (by
        norm_num [halfThirdScalingBlockRGPackage, halfThirdScalingBlockBounds,
          FinitePlusTailBlockBounds.decoupledScaling,
          FinitePlusTailBlockBounds.ofDecoupled])
      (by
        norm_num [halfThirdScalingBlockRGPackage, halfThirdScalingBlockBounds,
          FinitePlusTailBlockBounds.decoupledScaling,
          FinitePlusTailBlockBounds.ofDecoupled])
      (by
        norm_num [halfThirdScalingBlockRGPackage, halfThirdScalingBlockBounds,
          FinitePlusTailBlockBounds.decoupledScaling,
          FinitePlusTailBlockBounds.ofDecoupled])
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num [halfThirdScalingBlockRGPackage])
      halfThirdScalingBlockScale halfThirdScalingModel hν


noncomputable def halfThirdScalingBlockRGCertificate :
    RGCertificate halfThirdScalingModel :=
  halfThirdScalingBlockRGPackage.certificate
    halfThirdScalingBlockScale halfThirdScalingModel



theorem halfThirdScalingBlockRGCertificate_fixedPointEnclosure :
    halfThirdScalingBlockRGCertificate.FixedPointEnclosure := by
  simpa [halfThirdScalingBlockRGCertificate] using
    halfThirdScalingBlockRGPackage.certificate_fixedPointEnclosure
      halfThirdScalingBlockScale halfThirdScalingModel



theorem halfThirdScalingBlockRGCertificate_hyperbolicSplitting :
    halfThirdScalingBlockRGCertificate.HyperbolicSplitting :=
  halfThirdScalingBlockRGCertificate.hyperbolicSplitting_of_thermal_gt_one



theorem halfThirdScalingBlockRGCertificate_linearizationEnclosure :
    halfThirdScalingBlockRGCertificate.LinearizationEnclosure :=
  halfThirdScalingBlockRGCertificate.linearizationEnclosure_of_thermal_gt_one



theorem halfThirdScalingBlockRGCertificate_cone_iterate
    {η : ℝ} (hη : 0 ≤ η)
    {x : halfThirdScalingBlockRGCertificate.H.carrier}
    (hx : halfThirdScalingBlockRGPackage.hyperbolicSplitting.cone η x)
    (k : ℕ) :
    halfThirdScalingBlockRGPackage.hyperbolicSplitting.cone η
      (((halfThirdScalingBlockRGCertificate.R.map)^[k]) x) := by
  simpa [halfThirdScalingBlockRGCertificate] using
    halfThirdScalingBlockRGPackage.certificate_cone_iterate
      halfThirdScalingBlockScale halfThirdScalingModel hη hx k



theorem halfThirdScalingBlockRGCertificate_valid_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      halfThirdScalingBlockRGCertificate.RGToExponentBridge correlationLength) :
    halfThirdScalingBlockRGCertificate.Valid correlationLength := by
  simpa [halfThirdScalingBlockRGCertificate] using
    halfThirdScalingBlockRGPackage.certificate_valid_of_bridge
      halfThirdScalingBlockScale halfThirdScalingModel correlationLength hbridge



theorem halfThirdScalingBlockRGCertificate_hasCriticalNu_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      halfThirdScalingBlockRGCertificate.RGToExponentBridge correlationLength) :
    HasCriticalNu halfThirdScalingModel correlationLength
      halfThirdScalingBlockRGCertificate.predictedExponent :=
  (halfThirdScalingBlockRGCertificate_valid_of_bridge
    correlationLength hbridge).hasCriticalNu



theorem halfThirdScalingBlockRGCertificate_rgToExponentBridge_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu halfThirdScalingModel correlationLength
        halfThirdScalingBlockRGCertificate.predictedExponent) :
    halfThirdScalingBlockRGCertificate.RGToExponentBridge
      correlationLength := by
  simpa [halfThirdScalingBlockRGCertificate] using
    halfThirdScalingBlockRGPackage.certificate_rgToExponentBridge_of_hasCriticalNu
      halfThirdScalingBlockScale halfThirdScalingModel correlationLength hν



theorem halfThirdScalingBlockRGCertificate_valid_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu halfThirdScalingModel correlationLength
        halfThirdScalingBlockRGCertificate.predictedExponent) :
    halfThirdScalingBlockRGCertificate.Valid correlationLength := by
  simpa [halfThirdScalingBlockRGCertificate] using
    halfThirdScalingBlockRGPackage.certificate_valid_of_hasCriticalNu
      halfThirdScalingBlockScale halfThirdScalingModel correlationLength hν



theorem halfThirdScalingBlockRGCertificate_predictedExponent_eq_rg :
    halfThirdScalingBlockRGCertificate.predictedExponent =
      halfThirdScalingRGCertificate.predictedExponent := by
  calc
    halfThirdScalingBlockRGCertificate.predictedExponent =
        predictedNu halfThirdScalingBlockScale 3 := by
      simpa [halfThirdScalingBlockRGCertificate] using
        halfThirdScalingBlockRGPackage_predictedExponent_eq
    _ = halfThirdScalingRGCertificate.predictedExponent := by
      symm
      exact halfThirdScalingRGCertificate_predictedExponent_eq



noncomputable def halfThirdScalingBlockRGAnalyticBridgeInputs :
    RGCertificate.AnalyticBridgeInputs halfThirdScalingBlockRGCertificate
      halfThirdScalingCorrelationLength
      halfThirdScalingToyRGCovariance
      halfThirdScalingToyStableManifoldControl
      halfThirdScalingToyMicroscopicOrbitEntry
      halfThirdScalingToySubcriticalMassBridge :=
  RGCertificate.AnalyticBridgeInputs.congr_predictedExponent
    halfThirdScalingBlockRGCertificate_predictedExponent_eq_rg
    halfThirdScalingAnalyticBridgeInputs



theorem halfThirdScalingBlockRGCertificate_bridge_from_analyticInputs :
    halfThirdScalingBlockRGCertificate.RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  RGCertificate.AnalyticBridgeInputs.rgToExponentBridge
    halfThirdScalingBlockRGAnalyticBridgeInputs



theorem halfThirdScalingBlockRGCertificate_valid_from_analyticInputs :
    halfThirdScalingBlockRGCertificate.Valid halfThirdScalingCorrelationLength :=
  RGCertificate.AnalyticBridgeInputs.valid_of_checks
    halfThirdScalingBlockRGAnalyticBridgeInputs
    trivial trivial halfThirdScalingBlockRGCertificate_fixedPointEnclosure
    halfThirdScalingBlockRGCertificate_linearizationEnclosure
    halfThirdScalingBlockRGCertificate_hyperbolicSplitting trivial



theorem halfThirdScalingBlockRGCertificate_hasCriticalNu_from_analyticInputs :
    HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength
      halfThirdScalingBlockRGCertificate.predictedExponent :=
  RGCertificate.AnalyticBridgeInputs.hasCriticalNu
    halfThirdScalingBlockRGAnalyticBridgeInputs



noncomputable def halfThirdScalingBlockRGAnalyticPrefactorBridgeInputs :
    RGCertificate.AnalyticPrefactorBridgeInputs
      halfThirdScalingBlockRGCertificate halfThirdScalingCorrelationLength
      halfThirdScalingPrefactor
      halfThirdScalingToyRGCovariance
      halfThirdScalingToyStableManifoldControl
      halfThirdScalingToyMicroscopicOrbitEntry
      halfThirdScalingToySubcriticalMassBridge :=
  RGCertificate.AnalyticPrefactorBridgeInputs.congr_predictedExponent
    halfThirdScalingBlockRGCertificate_predictedExponent_eq_rg
    halfThirdScalingAnalyticPrefactorBridgeInputs



theorem halfThirdScalingBlockRGCertificate_bridge_from_prefactorInputs :
    halfThirdScalingBlockRGCertificate.RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  RGCertificate.AnalyticPrefactorBridgeInputs.rgToExponentBridge
    halfThirdScalingBlockRGAnalyticPrefactorBridgeInputs



theorem halfThirdScalingBlockRGCertificate_valid_from_prefactorInputs :
    halfThirdScalingBlockRGCertificate.Valid halfThirdScalingCorrelationLength :=
  RGCertificate.AnalyticPrefactorBridgeInputs.valid_of_checks
    halfThirdScalingBlockRGAnalyticPrefactorBridgeInputs
    trivial trivial halfThirdScalingBlockRGCertificate_fixedPointEnclosure
    halfThirdScalingBlockRGCertificate_linearizationEnclosure
    halfThirdScalingBlockRGCertificate_hyperbolicSplitting trivial



theorem halfThirdScalingBlockRGCertificate_hasCriticalNu_from_prefactorInputs :
    HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength
      halfThirdScalingBlockRGCertificate.predictedExponent :=
  RGCertificate.AnalyticPrefactorBridgeInputs.hasCriticalNu
    halfThirdScalingBlockRGAnalyticPrefactorBridgeInputs



noncomputable def halfThirdScalingBlockRGAnalyticMassBridgeInputs :
    RGCertificate.AnalyticMassBridgeInputs
      halfThirdScalingBlockRGCertificate halfThirdScalingCorrelationLength
      halfThirdScalingMass halfThirdScalingMassPrefactor
      halfThirdScalingToyRGCovariance
      halfThirdScalingToyStableManifoldControl
      halfThirdScalingToyMicroscopicOrbitEntry
      halfThirdScalingToySubcriticalMassBridge :=
  RGCertificate.AnalyticMassBridgeInputs.congr_predictedExponent
    halfThirdScalingBlockRGCertificate_predictedExponent_eq_rg
    halfThirdScalingAnalyticMassBridgeInputs



theorem halfThirdScalingBlockRGCertificate_bridge_from_massInputs :
    halfThirdScalingBlockRGCertificate.RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  RGCertificate.AnalyticMassBridgeInputs.rgToExponentBridge
    halfThirdScalingBlockRGAnalyticMassBridgeInputs



theorem halfThirdScalingBlockRGCertificate_valid_from_massInputs :
    halfThirdScalingBlockRGCertificate.Valid halfThirdScalingCorrelationLength :=
  RGCertificate.AnalyticMassBridgeInputs.valid_of_checks
    halfThirdScalingBlockRGAnalyticMassBridgeInputs
    trivial trivial halfThirdScalingBlockRGCertificate_fixedPointEnclosure
    halfThirdScalingBlockRGCertificate_linearizationEnclosure
    halfThirdScalingBlockRGCertificate_hyperbolicSplitting trivial



theorem halfThirdScalingBlockRGCertificate_hasCriticalNu_from_massInputs :
    HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength
      halfThirdScalingBlockRGCertificate.predictedExponent :=
  RGCertificate.AnalyticMassBridgeInputs.hasCriticalNu
    halfThirdScalingBlockRGAnalyticMassBridgeInputs


theorem halfThirdScalingCertificate_zero_residual :
    (halfThirdScalingCertificate.map zeroState).dist zeroState ≤ 0 := by
  rw [halfThirdScalingCertificate_map_zero, FinitePlusTailState.dist_self]


theorem halfThirdScalingCertificate_unitCenter_residual :
    (halfThirdScalingCertificate.map unitCenterState).dist unitCenterState ≤
      (1 : ℝ) / 2 := by
  norm_num [unitCenterState, halfThirdScalingCertificate,
    FinitePlusTailLipschitzCertificate.decoupledScaling,
    FinitePlusTailLipschitzCertificate.ofDecoupled,
    FinitePlusTailState.dist, FiniteContraction.l1Dist,
    RatInterval.supNormVec, SummableTail.dist, SummableTail.scale]



theorem halfThirdScalingCertificate_fixedPoint_eq_zero :
    halfThirdScalingCertificate.fixedPoint = zeroState := by
  symm
  exact halfThirdScalingCertificate.eq_fixedPoint_of_isFixed
    halfThirdScalingCertificate_map_zero


theorem halfThirdScalingCertificate_exists_unique_fixedPoint :
    ∃! p : FinitePlusTailState 1 ℕ,
      halfThirdScalingCertificate.map p = p :=
  halfThirdScalingCertificate.exists_unique_fixedPoint



theorem halfThirdScalingCertificate_mapsClosedBall_zero {radius : ℝ}
    (hradius : 0 ≤ radius) :
    FinitePlusTailState.MapsClosedBall
      halfThirdScalingCertificate.map zeroState radius := by
  apply halfThirdScalingCertificate.mapsClosedBall_of_residual_and_lipschitz
    (center := zeroState) (residual := 0)
  · exact halfThirdScalingCertificate_zero_residual
  · rw [halfThirdScalingCertificate_c_eq]
    nlinarith


noncomputable def halfThirdScalingBlockBoundsClosedBallCertificate
    {radius : ℝ} (hradius : 0 ≤ radius) :
    FinitePlusTailClosedBallContractionCertificate 1 ℕ :=
  halfThirdScalingBlockBounds.toClosedBallCertificate
    (c := (1 : ℝ) / 2)
    (by norm_num)
    (by norm_num)
    halfThirdScalingBlockBounds_finite_column
    halfThirdScalingBlockBounds_tail_column
    zeroState
    hradius
    halfThirdScalingBlockBounds_zero_residual
    (by nlinarith)



theorem halfThirdScalingBlockBounds_mapsClosedBall_zero {radius : ℝ}
    (hradius : 0 ≤ radius) :
    FinitePlusTailState.MapsClosedBall
      halfThirdScalingBlockBounds.map zeroState radius := by
  simpa [halfThirdScalingBlockBoundsClosedBallCertificate] using
    (halfThirdScalingBlockBoundsClosedBallCertificate hradius).mapsClosedBall



theorem halfThirdScalingBlockBoundsClosedBallCertificate_fixedPoint_isFixed
    {radius : ℝ} (hradius : 0 ≤ radius) :
    halfThirdScalingBlockBounds.map
      (halfThirdScalingBlockBoundsClosedBallCertificate hradius).fixedPoint =
      (halfThirdScalingBlockBoundsClosedBallCertificate hradius).fixedPoint := by
  simpa [halfThirdScalingBlockBoundsClosedBallCertificate] using
    halfThirdScalingBlockBounds.toClosedBallCertificate_fixedPoint_isFixed
      (c := (1 : ℝ) / 2)
      (by norm_num)
      (by norm_num)
      halfThirdScalingBlockBounds_finite_column
      halfThirdScalingBlockBounds_tail_column
      zeroState
      hradius
      halfThirdScalingBlockBounds_zero_residual
      (by nlinarith)


noncomputable def halfThirdScalingClosedBallCertificate {radius : ℝ}
    (hradius : 0 ≤ radius) :
    FinitePlusTailClosedBallContractionCertificate 1 ℕ :=
  FinitePlusTailClosedBallContractionCertificate.ofFixedCenter
    halfThirdScalingCertificate zeroState hradius
    halfThirdScalingCertificate_map_zero


noncomputable def halfThirdScalingRadiusZeroClosedBallCertificate :
    FinitePlusTailClosedBallContractionCertificate 1 ℕ :=
  halfThirdScalingClosedBallCertificate (radius := 0) (by norm_num)


noncomputable def halfThirdScalingRadiusOneFromZeroClosedBallCertificate :
    FinitePlusTailClosedBallContractionCertificate 1 ℕ :=
  halfThirdScalingRadiusZeroClosedBallCertificate.with_larger_radius
    (radius' := 1)
    (by
      norm_num [halfThirdScalingRadiusZeroClosedBallCertificate,
        halfThirdScalingClosedBallCertificate,
        FinitePlusTailClosedBallContractionCertificate.ofFixedCenter,
        FinitePlusTailClosedBallContractionCertificate.ofResidualBound])



noncomputable def halfThirdScalingUnitClosedBallCertificate :
    FinitePlusTailClosedBallContractionCertificate 1 ℕ :=
  FinitePlusTailClosedBallContractionCertificate.ofResidualMargin
    halfThirdScalingCertificate unitCenterState
    (radius := 1)
    (by norm_num)
    (by
      convert halfThirdScalingCertificate_unitCenter_residual using 1
      norm_num [halfThirdScalingCertificate_c_eq])



noncomputable def halfThirdScalingZeroClosedBallRGPackage :
    FinitePlusTailClosedBallRGPackage 1 ℕ where
  closedBall := halfThirdScalingRadiusOneFromZeroClosedBallCertificate
  thermal := 3
  thermal_gt_one := by norm_num


noncomputable def halfThirdScalingZeroClosedBallRGCertificate :
    RGCertificate halfThirdScalingModel :=
  halfThirdScalingZeroClosedBallRGPackage.certificate
    halfThirdScalingBlockScale halfThirdScalingModel



theorem halfThirdScalingZeroClosedBallRGCertificate_fixedPointEnclosure :
    halfThirdScalingZeroClosedBallRGCertificate.FixedPointEnclosure := by
  simpa [halfThirdScalingZeroClosedBallRGCertificate] using
    FinitePlusTailClosedBallContractionCertificate.certificate_fixedPointEnclosure
      halfThirdScalingRadiusOneFromZeroClosedBallCertificate
      halfThirdScalingBlockScale halfThirdScalingModel 3 (by norm_num)



theorem halfThirdScalingZeroClosedBallRGCertificate_fixedPoint_mem :
    FinitePlusTailState.ClosedBall zeroState 1
      halfThirdScalingZeroClosedBallRGCertificate.fixedPointData.fixedPoint := by
  simpa [halfThirdScalingZeroClosedBallRGCertificate,
    halfThirdScalingRadiusOneFromZeroClosedBallCertificate,
    halfThirdScalingRadiusZeroClosedBallCertificate,
    halfThirdScalingClosedBallCertificate] using
    FinitePlusTailClosedBallContractionCertificate.certificate_fixedPoint_mem_closedBall
      halfThirdScalingRadiusOneFromZeroClosedBallCertificate
      halfThirdScalingBlockScale halfThirdScalingModel 3 (by norm_num)



theorem halfThirdScalingZeroClosedBallRGCertificate_iterate_mem
    {x : halfThirdScalingZeroClosedBallRGCertificate.H.carrier}
    (hx : FinitePlusTailState.ClosedBall zeroState 1 x) (k : ℕ) :
    FinitePlusTailState.ClosedBall zeroState 1
      (((halfThirdScalingZeroClosedBallRGCertificate.R.map)^[k]) x) := by
  simpa [halfThirdScalingZeroClosedBallRGCertificate,
    halfThirdScalingRadiusOneFromZeroClosedBallCertificate,
    halfThirdScalingRadiusZeroClosedBallCertificate,
    halfThirdScalingClosedBallCertificate] using
    FinitePlusTailClosedBallContractionCertificate.certificate_iterate_mem_closedBall
      halfThirdScalingRadiusOneFromZeroClosedBallCertificate
      halfThirdScalingBlockScale halfThirdScalingModel 3 (by norm_num) hx k



theorem halfThirdScalingZeroClosedBallRGPackage_fixedPoint_mem :
    FinitePlusTailState.ClosedBall
      halfThirdScalingZeroClosedBallRGPackage.closedBall.center
      halfThirdScalingZeroClosedBallRGPackage.closedBall.radius
      (halfThirdScalingZeroClosedBallRGPackage.certificate
        halfThirdScalingBlockScale
        halfThirdScalingModel).fixedPointData.fixedPoint :=
  halfThirdScalingZeroClosedBallRGPackage.certificate_fixedPoint_mem_closedBall
    halfThirdScalingBlockScale halfThirdScalingModel



theorem halfThirdScalingZeroClosedBallRGPackage_iterate_mem
    {x :
      (halfThirdScalingZeroClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).H.carrier}
    (hx :
      FinitePlusTailState.ClosedBall
        halfThirdScalingZeroClosedBallRGPackage.closedBall.center
        halfThirdScalingZeroClosedBallRGPackage.closedBall.radius x)
    (k : ℕ) :
    FinitePlusTailState.ClosedBall
      halfThirdScalingZeroClosedBallRGPackage.closedBall.center
      halfThirdScalingZeroClosedBallRGPackage.closedBall.radius
      ((((halfThirdScalingZeroClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).R.map)^[k]) x) :=
  halfThirdScalingZeroClosedBallRGPackage.certificate_iterate_mem_closedBall
    halfThirdScalingBlockScale halfThirdScalingModel hx k



theorem halfThirdScalingZeroClosedBallRGPackage_thermalEigenvalue_eq :
    (halfThirdScalingZeroClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).thermalEigenvalue =
        3 :=
  halfThirdScalingZeroClosedBallRGPackage.certificate_thermalEigenvalue_eq
    halfThirdScalingBlockScale halfThirdScalingModel



theorem halfThirdScalingZeroClosedBallRGPackage_scale_eq :
    (halfThirdScalingZeroClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).scale =
        halfThirdScalingBlockScale :=
  halfThirdScalingZeroClosedBallRGPackage.certificate_scale_eq
    halfThirdScalingBlockScale halfThirdScalingModel



theorem halfThirdScalingZeroClosedBallRGPackage_predictedExponent_eq :
    (halfThirdScalingZeroClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent =
        predictedNu halfThirdScalingBlockScale 3 :=
  halfThirdScalingZeroClosedBallRGPackage.certificate_predictedExponent_eq
    halfThirdScalingBlockScale halfThirdScalingModel



noncomputable def halfThirdScalingUnitClosedBallRGPackage :
    FinitePlusTailClosedBallRGPackage 1 ℕ where
  closedBall := halfThirdScalingUnitClosedBallCertificate
  thermal := 3
  thermal_gt_one := by norm_num



noncomputable def halfThirdScalingUnitClosedBallRGPackage_relaxedRadius :
    FinitePlusTailClosedBallRGPackage 1 ℕ :=
  halfThirdScalingUnitClosedBallRGPackage.with_larger_radius
    (radius' := 2)
    (by
      norm_num [halfThirdScalingUnitClosedBallRGPackage,
        halfThirdScalingUnitClosedBallCertificate,
        FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
        FinitePlusTailClosedBallContractionCertificate.ofResidualBound])


theorem halfThirdScalingUnitClosedBallRGPackage_relaxedRadius_radius_eq :
    halfThirdScalingUnitClosedBallRGPackage_relaxedRadius.closedBall.radius =
      2 :=
  rfl


theorem halfThirdScalingUnitClosedBallRGPackage_relaxedRadius_thermal_eq :
    halfThirdScalingUnitClosedBallRGPackage_relaxedRadius.thermal = 3 :=
  rfl



theorem
    halfThirdScalingUnitClosedBallRGPackage_relaxedRadius_predictedExponent_eq :
    (halfThirdScalingUnitClosedBallRGPackage_relaxedRadius.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent =
        predictedNu halfThirdScalingBlockScale 3 :=
  FinitePlusTailClosedBallRGPackage.certificate_predictedExponent_eq
    halfThirdScalingUnitClosedBallRGPackage_relaxedRadius
    halfThirdScalingBlockScale halfThirdScalingModel



theorem halfThirdScalingUnitClosedBallRGPackage_relaxedRadius_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu halfThirdScalingModel correlationLength
        (halfThirdScalingUnitClosedBallRGPackage.certificate
          halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent) :
    HasCriticalNu halfThirdScalingModel correlationLength
      (halfThirdScalingUnitClosedBallRGPackage_relaxedRadius.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  simpa [halfThirdScalingUnitClosedBallRGPackage_relaxedRadius] using
    halfThirdScalingUnitClosedBallRGPackage.with_larger_radius_hasCriticalNu
      (radius' := 2)
      (by
        norm_num [halfThirdScalingUnitClosedBallRGPackage,
          halfThirdScalingUnitClosedBallCertificate,
          FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
          FinitePlusTailClosedBallContractionCertificate.ofResidualBound])
      halfThirdScalingBlockScale halfThirdScalingModel hν



noncomputable def halfThirdScalingUnitClosedBallRGPackage_relaxedResidual :
    FinitePlusTailClosedBallRGPackage 1 ℕ :=
  halfThirdScalingUnitClosedBallRGPackage_relaxedRadius.with_larger_residual
    (residual' := (3 : ℝ) / 4)
    (by
      norm_num [halfThirdScalingUnitClosedBallRGPackage_relaxedRadius,
        halfThirdScalingUnitClosedBallRGPackage,
        halfThirdScalingUnitClosedBallCertificate,
        FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
        FinitePlusTailClosedBallContractionCertificate.ofResidualBound,
        halfThirdScalingCertificate_c_eq])
    (by
      norm_num [halfThirdScalingUnitClosedBallRGPackage_relaxedRadius,
        halfThirdScalingUnitClosedBallRGPackage,
        halfThirdScalingUnitClosedBallCertificate,
        FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
        FinitePlusTailClosedBallContractionCertificate.ofResidualBound,
        halfThirdScalingCertificate_c_eq])


theorem halfThirdScalingUnitClosedBallRGPackage_relaxedResidual_residual_eq :
    halfThirdScalingUnitClosedBallRGPackage_relaxedResidual.closedBall.residual =
      (3 : ℝ) / 4 :=
  rfl



theorem
    halfThirdScalingUnitClosedBallRGPackage_relaxedResidual_predictedExponent_eq :
    (halfThirdScalingUnitClosedBallRGPackage_relaxedResidual.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent =
        predictedNu halfThirdScalingBlockScale 3 :=
  FinitePlusTailClosedBallRGPackage.certificate_predictedExponent_eq
    halfThirdScalingUnitClosedBallRGPackage_relaxedResidual
    halfThirdScalingBlockScale halfThirdScalingModel



theorem halfThirdScalingUnitClosedBallRGPackage_relaxedResidual_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu halfThirdScalingModel correlationLength
        (halfThirdScalingUnitClosedBallRGPackage_relaxedRadius.certificate
          halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent) :
    HasCriticalNu halfThirdScalingModel correlationLength
      (halfThirdScalingUnitClosedBallRGPackage_relaxedResidual.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  simpa [halfThirdScalingUnitClosedBallRGPackage_relaxedResidual] using
    FinitePlusTailClosedBallRGPackage.with_larger_residual_hasCriticalNu
      halfThirdScalingUnitClosedBallRGPackage_relaxedRadius
      (residual' := (3 : ℝ) / 4)
      (by
        norm_num [halfThirdScalingUnitClosedBallRGPackage_relaxedRadius,
          halfThirdScalingUnitClosedBallRGPackage,
          halfThirdScalingUnitClosedBallCertificate,
          FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
          FinitePlusTailClosedBallContractionCertificate.ofResidualBound,
          halfThirdScalingCertificate_c_eq])
      (by
        norm_num [halfThirdScalingUnitClosedBallRGPackage_relaxedRadius,
          halfThirdScalingUnitClosedBallRGPackage,
          halfThirdScalingUnitClosedBallCertificate,
          FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
          FinitePlusTailClosedBallContractionCertificate.ofResidualBound,
          halfThirdScalingCertificate_c_eq])
      halfThirdScalingBlockScale halfThirdScalingModel hν



def tableClosedBallCouplingCutoff : TailCutoff where
  radius := 0
  maxDegree := 0
  maxRange := 0

noncomputable instance tableClosedBallCouplingCutoffDecidableEq :
    DecidableEq (FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff) :=
  Classical.decEq _




noncomputable def zeroTableClosedBallRGPackage :
    @InfiniteTailTableClosedBallRGPackage Unit
      (BoundedPolymerCase.StableKey
        tableClosedBallCouplingCutoff.maxDegree
        tableClosedBallCouplingCutoff.maxRange)
      (FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff) ℕ _ _
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) 1 where
  tableWitness :=
    InfiniteTailStableKeyPackageExample.rawRowsZeroInfiniteTailPackage
      (d := 1) tableClosedBallCouplingCutoff
  closedBallRG := halfThirdScalingUnitClosedBallRGPackage
  tableBudget_le_residual := by
    rw [rawRowsZeroInfiniteTailPackage_tableCertifiedTotalBound_eq_zero]
    norm_num [halfThirdScalingUnitClosedBallRGPackage,
      halfThirdScalingUnitClosedBallCertificate,
      FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
      FinitePlusTailClosedBallContractionCertificate.ofResidualBound,
      halfThirdScalingCertificate_c_eq]



theorem zeroTableClosedBallRGPackage_tailTotalTsum_le_residual :
    zeroTableClosedBallRGPackage.tailTotalTsum ≤
      zeroTableClosedBallRGPackage.closedBallResidual :=
  zeroTableClosedBallRGPackage.tailTotalTsum_le_closedBallResidual



theorem zeroTableClosedBallRGPackage_predictedExponent_eq :
    (zeroTableClosedBallRGPackage.certificate
      FiniteWitnessPackageExample.exampleScale).predictedExponent =
        predictedNu FiniteWitnessPackageExample.exampleScale 3 :=
  zeroTableClosedBallRGPackage.certificate_predictedExponent_eq
    FiniteWitnessPackageExample.exampleScale



noncomputable def generatedStableKeyEmptySupport :
    Finset (FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff) :=
  ∅


theorem generatedStableKeyEmptySupport_saturated :
    ∀ a,
      classifyFiniteCutoffStableKey tableClosedBallCouplingCutoff a ∈
          generatedStableKeyEmptySupport.image
            (classifyFiniteCutoffStableKey tableClosedBallCouplingCutoff) →
        a ∈ generatedStableKeyEmptySupport := by
  intro a h
  simp [generatedStableKeyEmptySupport] at h



noncomputable def generatedStableKeyEmptyInfiniteTailPackage :
    InfiniteTailTableWitnessPackage
      (Case := BoundedPolymerCase.StableKey
        tableClosedBallCouplingCutoff.maxDegree
        tableClosedBallCouplingCutoff.maxRange)
      (α := FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  generatedStableKeyInfiniteTailPackage
    (d := 1)
    tableClosedBallCouplingCutoff
    generatedStableKeyEmptySupport
    generatedStableKeyEmptySupport_saturated


theorem generatedStableKeyEmptyInfiniteTailPackage_budget_eq_zero :
    generatedStableKeyEmptyInfiniteTailPackage.tableCertifiedTotalBound =
      0 := by
  rw [generatedStableKeyEmptyInfiniteTailPackage]
  rw [generatedStableKeyInfiniteTailPackage_tableCertifiedTotalBound_eq_card]
  simp [generatedStableKeyEmptySupport]




noncomputable def generatedStableKeyTableClosedBallRGPackage :
    @InfiniteTailTableClosedBallRGPackage Unit
      (BoundedPolymerCase.StableKey
        tableClosedBallCouplingCutoff.maxDegree
        tableClosedBallCouplingCutoff.maxRange)
      (FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff) ℕ _ _
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) 1 where
  tableWitness := generatedStableKeyEmptyInfiniteTailPackage
  closedBallRG := halfThirdScalingUnitClosedBallRGPackage
  tableBudget_le_residual := by
    rw [generatedStableKeyEmptyInfiniteTailPackage_budget_eq_zero]
    norm_num [halfThirdScalingUnitClosedBallRGPackage,
      halfThirdScalingUnitClosedBallCertificate,
      FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
      FinitePlusTailClosedBallContractionCertificate.ofResidualBound,
      halfThirdScalingCertificate_c_eq]



theorem generatedStableKeyTableClosedBallRGPackage_tailTotalTsum_le_residual :
    generatedStableKeyTableClosedBallRGPackage.tailTotalTsum ≤
      generatedStableKeyTableClosedBallRGPackage.closedBallResidual :=
  generatedStableKeyTableClosedBallRGPackage.tailTotalTsum_le_closedBallResidual



theorem generatedStableKeyTableClosedBallRGPackage_predictedExponent_eq :
    (generatedStableKeyTableClosedBallRGPackage.certificate
      FiniteWitnessPackageExample.exampleScale).predictedExponent =
        predictedNu FiniteWitnessPackageExample.exampleScale 3 :=
  generatedStableKeyTableClosedBallRGPackage.certificate_predictedExponent_eq
    FiniteWitnessPackageExample.exampleScale



noncomputable def zeroTableClosedBallRGPackage_radiusFive :
    @InfiniteTailTableClosedBallRGPackage Unit
      (BoundedPolymerCase.StableKey
        tableClosedBallCouplingCutoff.maxDegree
        tableClosedBallCouplingCutoff.maxRange)
      (FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff) ℕ _ _
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) 1 :=
  zeroTableClosedBallRGPackage.with_larger_closedBallRadius
    (radius' := 5)
    (by
      norm_num [zeroTableClosedBallRGPackage,
        halfThirdScalingUnitClosedBallRGPackage,
        halfThirdScalingUnitClosedBallCertificate,
        FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
        FinitePlusTailClosedBallContractionCertificate.ofResidualBound])


theorem zeroTableClosedBallRGPackage_radiusFive_radius_eq :
    zeroTableClosedBallRGPackage_radiusFive.closedBallRadius = 5 :=
  rfl


theorem zeroTableClosedBallRGPackage_radiusFive_residual_eq :
    zeroTableClosedBallRGPackage_radiusFive.closedBallResidual =
      (1 : ℝ) / 2 :=
  by
    norm_num [zeroTableClosedBallRGPackage_radiusFive,
      zeroTableClosedBallRGPackage, halfThirdScalingUnitClosedBallRGPackage,
      halfThirdScalingUnitClosedBallCertificate,
      InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius,
      InfiniteTailTableClosedBallRGPackage.closedBallResidual,
      FinitePlusTailClosedBallRGPackage.with_larger_radius,
      FinitePlusTailClosedBallContractionCertificate.with_larger_radius,
      FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
      FinitePlusTailClosedBallContractionCertificate.ofResidualBound,
      halfThirdScalingCertificate_c_eq]


theorem zeroTableClosedBallRGPackage_radiusFive_contraction_c_eq :
    zeroTableClosedBallRGPackage_radiusFive.closedBallContraction.c =
      (1 : ℝ) / 2 :=
  by
    norm_num [zeroTableClosedBallRGPackage_radiusFive,
      zeroTableClosedBallRGPackage, halfThirdScalingUnitClosedBallRGPackage,
      halfThirdScalingUnitClosedBallCertificate,
      InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius,
      InfiniteTailTableClosedBallRGPackage.closedBallContraction,
      FinitePlusTailClosedBallRGPackage.with_larger_radius,
      FinitePlusTailClosedBallContractionCertificate.with_larger_radius,
      FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
      FinitePlusTailClosedBallContractionCertificate.ofResidualBound,
      halfThirdScalingCertificate_c_eq]



noncomputable def zeroTableClosedBallRGPackage_radiusFiveResidualTwo :
    @InfiniteTailTableClosedBallRGPackage Unit
      (BoundedPolymerCase.StableKey
        tableClosedBallCouplingCutoff.maxDegree
        tableClosedBallCouplingCutoff.maxRange)
      (FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff) ℕ _ _
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) 1 :=
  zeroTableClosedBallRGPackage_radiusFive.with_larger_closedBallResidual
    (residual' := 2)
    (by
      change zeroTableClosedBallRGPackage_radiusFive.closedBallResidual ≤ 2
      rw [zeroTableClosedBallRGPackage_radiusFive_residual_eq]
      norm_num)
    (by
      change
        2 + zeroTableClosedBallRGPackage_radiusFive.closedBallContraction.c *
            zeroTableClosedBallRGPackage_radiusFive.closedBallRadius ≤
          zeroTableClosedBallRGPackage_radiusFive.closedBallRadius
      rw [zeroTableClosedBallRGPackage_radiusFive_contraction_c_eq,
        zeroTableClosedBallRGPackage_radiusFive_radius_eq]
      norm_num)


theorem zeroTableClosedBallRGPackage_radiusFiveResidualTwo_residual_eq :
    zeroTableClosedBallRGPackage_radiusFiveResidualTwo.closedBallResidual =
      2 :=
  rfl



theorem zeroTableClosedBallRGPackage_radiusFiveResidualTwo_thermal_eq :
    zeroTableClosedBallRGPackage_radiusFiveResidualTwo.closedBallRG.thermal =
      3 :=
  rfl



noncomputable def zeroTableClosedBallRGPackage_replacedTableWitness :
    @InfiniteTailTableClosedBallRGPackage Unit
      (BoundedPolymerCase.StableKey
        tableClosedBallCouplingCutoff.maxDegree
        tableClosedBallCouplingCutoff.maxRange)
      (FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff) ℕ _ _
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) 1 :=
  zeroTableClosedBallRGPackage_radiusFiveResidualTwo.with_tableWitness
    (InfiniteTailStableKeyPackageExample.rawRowsZeroInfiniteTailPackage_replacedTailEnvelope
      (d := 1) tableClosedBallCouplingCutoff)
    (by
      rw [
        rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_budget_eq_two,
        zeroTableClosedBallRGPackage_radiusFiveResidualTwo_residual_eq])



theorem zeroTableClosedBallRGPackage_replacedTableWitness_thermal_eq :
    zeroTableClosedBallRGPackage_replacedTableWitness.closedBallRG.thermal =
      3 :=
  rfl


theorem zeroTableClosedBallRGPackage_replacedTableWitness_budget_eq_two :
    zeroTableClosedBallRGPackage_replacedTableWitness.tableCertifiedTotalBound =
      2 := by
  rw [zeroTableClosedBallRGPackage_replacedTableWitness]
  rw [InfiniteTailTableClosedBallRGPackage.with_tableWitness_tableCertifiedTotalBound]
  exact
    rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_budget_eq_two
      (d := 1) tableClosedBallCouplingCutoff



@[simp] theorem zeroTableClosedBallRGPackage_replacedTableWitness_certificate_eq
    (scale : BlockScale) :
    zeroTableClosedBallRGPackage_replacedTableWitness.certificate scale =
      zeroTableClosedBallRGPackage_radiusFiveResidualTwo.certificate scale :=
  rfl



theorem zeroTableClosedBallRGPackage_replacedTableWitness_predictedExponent_eq :
    (zeroTableClosedBallRGPackage_replacedTableWitness.certificate
      FiniteWitnessPackageExample.exampleScale).predictedExponent =
        predictedNu FiniteWitnessPackageExample.exampleScale 3 :=
  by
    simpa [
      zeroTableClosedBallRGPackage_replacedTableWitness_thermal_eq
    ] using
      InfiniteTailTableClosedBallRGPackage.certificate_predictedExponent_eq
        zeroTableClosedBallRGPackage_replacedTableWitness
        FiniteWitnessPackageExample.exampleScale



noncomputable def zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual :
    @InfiniteTailTableClosedBallRGPackage Unit
      (BoundedPolymerCase.StableKey
        tableClosedBallCouplingCutoff.maxDegree
        tableClosedBallCouplingCutoff.maxRange)
      (FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff) ℕ _ _
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) 1 :=
  zeroTableClosedBallRGPackage_radiusFive.with_tableWitness_as_closedBallResidual
      (rawRowsZeroInfiniteTailPackage_replacedTailEnvelope
        (d := 1) tableClosedBallCouplingCutoff)
      (by
        rw [zeroTableClosedBallRGPackage_radiusFive_residual_eq,
          rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_budget_eq_two]
        norm_num)
      (by
        rw [rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_budget_eq_two,
          zeroTableClosedBallRGPackage_radiusFive_contraction_c_eq,
          zeroTableClosedBallRGPackage_radiusFive_radius_eq]
        norm_num)



theorem
    zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_residual_eq_two :
    zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual.closedBallResidual =
      2 := by
  rw [zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual]
  rw [with_tableWitness_as_closedBallResidual_closedBallResidual]
  exact
    rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_budget_eq_two
      (d := 1) tableClosedBallCouplingCutoff


theorem zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_radius_eq :
    zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual.closedBallRadius =
      5 := by
  rw [zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual]
  rw [with_tableWitness_as_closedBallResidual_closedBallRadius]
  exact zeroTableClosedBallRGPackage_radiusFive_radius_eq


theorem
    zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_contraction_c_eq :
    (zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual.closedBallContraction).c =
      (1 : ℝ) / 2 := by
  rw [zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual]
  rw [with_tableWitness_as_closedBallResidual_closedBallContraction]
  exact zeroTableClosedBallRGPackage_radiusFive_contraction_c_eq


theorem zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_thermal_eq :
    zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual.closedBallRG.thermal =
      3 :=
  rfl



theorem
    zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_budget_eq_two :
    zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual.tableCertifiedTotalBound =
      2 := by
  rw [zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual]
  rw [with_tableWitness_as_closedBallResidual_tableCertifiedTotalBound]
  exact
    rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_budget_eq_two
      (d := 1) tableClosedBallCouplingCutoff



@[simp] theorem
    zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual_certificate_eq
    (scale : BlockScale) :
    zeroTableClosedBallRGPackage_replacedTableWitnessAsResidual.certificate scale =
      zeroTableClosedBallRGPackage_radiusFive.certificate scale :=
  rfl




noncomputable def generatedStableKeyReplacedInfiniteTailPackage :
    InfiniteTailTableWitnessPackage
      (Case := BoundedPolymerCase.StableKey
        tableClosedBallCouplingCutoff.maxDegree
        tableClosedBallCouplingCutoff.maxRange)
      (α := FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  generatedStableKeyInfiniteTailPackage_replacedTailEnvelope
    (d := 1)
    tableClosedBallCouplingCutoff
    generatedStableKeyEmptySupport
    generatedStableKeyEmptySupport_saturated


theorem generatedStableKeyReplacedInfiniteTailPackage_budget_eq_two :
    generatedStableKeyReplacedInfiniteTailPackage.tableCertifiedTotalBound =
      2 := by
  rw [generatedStableKeyReplacedInfiniteTailPackage]
  rw [
    generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two]
  simp [generatedStableKeyEmptySupport]



noncomputable def generatedStableKeyReplacedTableClosedBallRGPackage :
    @InfiniteTailTableClosedBallRGPackage Unit
      (BoundedPolymerCase.StableKey
        tableClosedBallCouplingCutoff.maxDegree
        tableClosedBallCouplingCutoff.maxRange)
      (FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff) ℕ _ _
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) 1 :=
  zeroTableClosedBallRGPackage_radiusFive.with_tableWitness_as_closedBallResidual
    generatedStableKeyReplacedInfiniteTailPackage
    (by
      rw [zeroTableClosedBallRGPackage_radiusFive_residual_eq,
        generatedStableKeyReplacedInfiniteTailPackage_budget_eq_two]
      norm_num)
    (by
      rw [generatedStableKeyReplacedInfiniteTailPackage_budget_eq_two,
        zeroTableClosedBallRGPackage_radiusFive_contraction_c_eq,
        zeroTableClosedBallRGPackage_radiusFive_radius_eq]
      norm_num)



theorem generatedStableKeyReplacedTableClosedBallRGPackage_residual_eq_two :
    generatedStableKeyReplacedTableClosedBallRGPackage.closedBallResidual =
      2 := by
  rw [generatedStableKeyReplacedTableClosedBallRGPackage]
  rw [with_tableWitness_as_closedBallResidual_closedBallResidual]
  exact generatedStableKeyReplacedInfiniteTailPackage_budget_eq_two



theorem generatedStableKeyReplacedTableClosedBallRGPackage_thermal_eq :
    generatedStableKeyReplacedTableClosedBallRGPackage.closedBallRG.thermal =
      3 :=
  rfl



theorem generatedStableKeyReplacedTableClosedBallRGPackage_radius_eq :
    generatedStableKeyReplacedTableClosedBallRGPackage.closedBallRadius =
      5 := by
  rw [generatedStableKeyReplacedTableClosedBallRGPackage]
  rw [with_tableWitness_as_closedBallResidual_closedBallRadius]
  exact zeroTableClosedBallRGPackage_radiusFive_radius_eq



theorem generatedStableKeyReplacedTableClosedBallRGPackage_contraction_c_eq :
    generatedStableKeyReplacedTableClosedBallRGPackage.closedBallContraction.c =
      (1 : ℝ) / 2 := by
  rw [generatedStableKeyReplacedTableClosedBallRGPackage]
  rw [with_tableWitness_as_closedBallResidual_closedBallContraction]
  exact zeroTableClosedBallRGPackage_radiusFive_contraction_c_eq



theorem generatedStableKeyReplacedTableClosedBallRGPackage_budget_eq_two :
    generatedStableKeyReplacedTableClosedBallRGPackage.tableCertifiedTotalBound =
      2 := by
  rw [generatedStableKeyReplacedTableClosedBallRGPackage]
  rw [with_tableWitness_as_closedBallResidual_tableCertifiedTotalBound]
  exact generatedStableKeyReplacedInfiniteTailPackage_budget_eq_two



theorem
    generatedStableKeyReplacedTableClosedBallRGPackage_budget_eq_residual :
    generatedStableKeyReplacedTableClosedBallRGPackage.tableCertifiedTotalBound =
      generatedStableKeyReplacedTableClosedBallRGPackage.closedBallResidual := by
  rw [generatedStableKeyReplacedTableClosedBallRGPackage_budget_eq_two,
    generatedStableKeyReplacedTableClosedBallRGPackage_residual_eq_two]



theorem
    generatedStableKeyReplacedTableClosedBallRGPackage_tailTotalTsum_le_residual :
    generatedStableKeyReplacedTableClosedBallRGPackage.tailTotalTsum ≤
      generatedStableKeyReplacedTableClosedBallRGPackage.closedBallResidual :=
  generatedStableKeyReplacedTableClosedBallRGPackage.tailTotalTsum_le_closedBallResidual



theorem
    generatedStableKeyReplacedTableClosedBallRGPackage_tailTotalTsum_radius :
    generatedStableKeyReplacedTableClosedBallRGPackage.tailTotalTsum +
        generatedStableKeyReplacedTableClosedBallRGPackage.closedBallContraction.c *
      generatedStableKeyReplacedTableClosedBallRGPackage.closedBallRadius ≤
      generatedStableKeyReplacedTableClosedBallRGPackage.closedBallRadius :=
  InfiniteTailTableClosedBallRGPackage.tailTotalTsum_plus_mul_radius_le_radius
    generatedStableKeyReplacedTableClosedBallRGPackage



@[simp] theorem generatedStableKeyReplacedTableClosedBallRGPackage_certificate_eq
    (scale : BlockScale) :
    generatedStableKeyReplacedTableClosedBallRGPackage.certificate scale =
      zeroTableClosedBallRGPackage_radiusFive.certificate scale :=
  rfl



theorem
    generatedStableKeyReplacedTableClosedBallRGPackage_predictedExponent_eq :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      FiniteWitnessPackageExample.exampleScale).predictedExponent =
        predictedNu FiniteWitnessPackageExample.exampleScale 3 :=
  by
    simpa using
      InfiniteTailTableClosedBallRGPackage.certificate_predictedExponent_eq
        generatedStableKeyReplacedTableClosedBallRGPackage
        FiniteWitnessPackageExample.exampleScale



noncomputable def genMinCubicKeyEmptySupport :
    Finset (FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff) :=
  ∅



theorem genMinCubicKeyEmptySupport_saturated :
    ∀ a,
      classifyFiniteCutoffMinimalCubicStableKey
          tableClosedBallCouplingCutoff a ∈
          genMinCubicKeyEmptySupport.image
            (classifyFiniteCutoffMinimalCubicStableKey
              tableClosedBallCouplingCutoff) →
        a ∈ genMinCubicKeyEmptySupport := by
  intro a h
  simp [genMinCubicKeyEmptySupport] at h



noncomputable def genMinCubicKeyEmptyInfiniteTailPackage :
    InfiniteTailTableWitnessPackage
      (Case := BoundedPolymerCase.StableKey
        tableClosedBallCouplingCutoff.maxDegree
        tableClosedBallCouplingCutoff.maxRange)
      (α := FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  generatedMinimalCubicStableKeyInfiniteTailPackage
    (d := 1)
    tableClosedBallCouplingCutoff
    genMinCubicKeyEmptySupport
    genMinCubicKeyEmptySupport_saturated



theorem genMinCubicKeyEmptyInfiniteTailPackage_budget_eq_zero :
    genMinCubicKeyEmptyInfiniteTailPackage.tableCertifiedTotalBound = 0 := by
  rw [genMinCubicKeyEmptyInfiniteTailPackage]
  rw [
    generatedMinimalCubicStableKeyInfiniteTailPackage_tableCertifiedTotalBound_eq_card]
  simp [genMinCubicKeyEmptySupport]



noncomputable def genMinCubicKeyTableClosedBallRGPackage :
    @InfiniteTailTableClosedBallRGPackage Unit
      (BoundedPolymerCase.StableKey
        tableClosedBallCouplingCutoff.maxDegree
        tableClosedBallCouplingCutoff.maxRange)
      (FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff) ℕ _ _
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) 1 where
  tableWitness := genMinCubicKeyEmptyInfiniteTailPackage
  closedBallRG := halfThirdScalingUnitClosedBallRGPackage
  tableBudget_le_residual := by
    rw [genMinCubicKeyEmptyInfiniteTailPackage_budget_eq_zero]
    norm_num [halfThirdScalingUnitClosedBallRGPackage,
      halfThirdScalingUnitClosedBallCertificate,
      FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
      FinitePlusTailClosedBallContractionCertificate.ofResidualBound,
      halfThirdScalingCertificate_c_eq]



theorem genMinCubicKeyTableClosedBallRGPackage_tailTotalTsum_le_residual :
    genMinCubicKeyTableClosedBallRGPackage.tailTotalTsum ≤
      genMinCubicKeyTableClosedBallRGPackage.closedBallResidual :=
  genMinCubicKeyTableClosedBallRGPackage.tailTotalTsum_le_closedBallResidual



theorem genMinCubicKeyTableClosedBallRGPackage_predictedExponent_eq :
    (genMinCubicKeyTableClosedBallRGPackage.certificate
      FiniteWitnessPackageExample.exampleScale).predictedExponent =
        predictedNu FiniteWitnessPackageExample.exampleScale 3 :=
  genMinCubicKeyTableClosedBallRGPackage.certificate_predictedExponent_eq
    FiniteWitnessPackageExample.exampleScale




noncomputable def genMinCubicKeyReplacedInfiniteTailPackage :
    InfiniteTailTableWitnessPackage
      (Case := BoundedPolymerCase.StableKey
        tableClosedBallCouplingCutoff.maxDegree
        tableClosedBallCouplingCutoff.maxRange)
      (α := FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope
    (d := 1)
    tableClosedBallCouplingCutoff
    genMinCubicKeyEmptySupport
    genMinCubicKeyEmptySupport_saturated



theorem genMinCubicKeyReplacedInfiniteTailPackage_budget_eq_two :
    genMinCubicKeyReplacedInfiniteTailPackage.tableCertifiedTotalBound =
      2 := by
  rw [genMinCubicKeyReplacedInfiniteTailPackage]
  rw [
    generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two]
  simp [genMinCubicKeyEmptySupport]



noncomputable def genMinCubicKeyReplacedTableClosedBallRGPackage :
    @InfiniteTailTableClosedBallRGPackage Unit
      (BoundedPolymerCase.StableKey
        tableClosedBallCouplingCutoff.maxDegree
        tableClosedBallCouplingCutoff.maxRange)
      (FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff) ℕ _ _
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) 1 :=
  zeroTableClosedBallRGPackage_radiusFive.with_tableWitness_as_closedBallResidual
    genMinCubicKeyReplacedInfiniteTailPackage
    (by
      rw [zeroTableClosedBallRGPackage_radiusFive_residual_eq,
        genMinCubicKeyReplacedInfiniteTailPackage_budget_eq_two]
      norm_num)
    (by
      rw [genMinCubicKeyReplacedInfiniteTailPackage_budget_eq_two,
        zeroTableClosedBallRGPackage_radiusFive_contraction_c_eq,
        zeroTableClosedBallRGPackage_radiusFive_radius_eq]
      norm_num)



theorem genMinCubicKeyReplacedTableClosedBallRGPackage_residual_eq_two :
    genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallResidual =
      2 := by
  rw [genMinCubicKeyReplacedTableClosedBallRGPackage]
  rw [with_tableWitness_as_closedBallResidual_closedBallResidual]
  exact genMinCubicKeyReplacedInfiniteTailPackage_budget_eq_two



theorem genMinCubicKeyReplacedTableClosedBallRGPackage_thermal_eq :
    genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallRG.thermal =
      3 :=
  rfl



theorem genMinCubicKeyReplacedTableClosedBallRGPackage_radius_eq :
    genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallRadius =
      5 := by
  rw [genMinCubicKeyReplacedTableClosedBallRGPackage]
  rw [with_tableWitness_as_closedBallResidual_closedBallRadius]
  exact zeroTableClosedBallRGPackage_radiusFive_radius_eq



theorem genMinCubicKeyReplacedTableClosedBallRGPackage_contraction_c_eq :
    genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallContraction.c =
      (1 : ℝ) / 2 := by
  rw [genMinCubicKeyReplacedTableClosedBallRGPackage]
  rw [with_tableWitness_as_closedBallResidual_closedBallContraction]
  exact zeroTableClosedBallRGPackage_radiusFive_contraction_c_eq



theorem genMinCubicKeyReplacedTableClosedBallRGPackage_budget_eq_two :
    genMinCubicKeyReplacedTableClosedBallRGPackage.tableCertifiedTotalBound =
      2 := by
  rw [genMinCubicKeyReplacedTableClosedBallRGPackage]
  rw [with_tableWitness_as_closedBallResidual_tableCertifiedTotalBound]
  exact genMinCubicKeyReplacedInfiniteTailPackage_budget_eq_two



theorem genMinCubicKeyReplacedTableClosedBallRGPackage_budget_eq_residual :
    genMinCubicKeyReplacedTableClosedBallRGPackage.tableCertifiedTotalBound =
      genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallResidual := by
  rw [genMinCubicKeyReplacedTableClosedBallRGPackage_budget_eq_two,
    genMinCubicKeyReplacedTableClosedBallRGPackage_residual_eq_two]



theorem genMinCubicKeyReplacedTableClosedBallRGPackage_tailTsum_le_residual :
    genMinCubicKeyReplacedTableClosedBallRGPackage.tailTotalTsum ≤
      genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallResidual :=
  genMinCubicKeyReplacedTableClosedBallRGPackage.tailTotalTsum_le_closedBallResidual



theorem genMinCubicKeyReplacedTableClosedBallRGPackage_tailTsum_radius :
    genMinCubicKeyReplacedTableClosedBallRGPackage.tailTotalTsum +
        genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallContraction.c *
      genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallRadius ≤
      genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallRadius :=
  InfiniteTailTableClosedBallRGPackage.tailTotalTsum_plus_mul_radius_le_radius
    genMinCubicKeyReplacedTableClosedBallRGPackage



@[simp] theorem genMinCubicKeyReplacedTableClosedBallRGPackage_certificate_eq
    (scale : BlockScale) :
    genMinCubicKeyReplacedTableClosedBallRGPackage.certificate scale =
      zeroTableClosedBallRGPackage_radiusFive.certificate scale :=
  rfl



theorem genMinCubicKeyReplacedTableClosedBallRGPackage_predictedExponent_eq :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      FiniteWitnessPackageExample.exampleScale).predictedExponent =
        predictedNu FiniteWitnessPackageExample.exampleScale 3 :=
  by
    simpa using
      InfiniteTailTableClosedBallRGPackage.certificate_predictedExponent_eq
        genMinCubicKeyReplacedTableClosedBallRGPackage
        FiniteWitnessPackageExample.exampleScale



noncomputable def genBoundedCaseEmptySupport :
    Finset (FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff) :=
  ∅



theorem genBoundedCaseEmptySupport_saturated :
    ∀ a,
      classifyFiniteCutoffCoordinate tableClosedBallCouplingCutoff a ∈
          genBoundedCaseEmptySupport.image
            (classifyFiniteCutoffCoordinate tableClosedBallCouplingCutoff) →
        a ∈ genBoundedCaseEmptySupport := by
  intro a h
  simp [genBoundedCaseEmptySupport] at h



noncomputable def genBoundedCaseEmptyInfiniteTailPackage :
    InfiniteTailTableWitnessPackage
      (Case := FiniteCutoffCase 1 tableClosedBallCouplingCutoff)
      (α := FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  generatedBoundedCaseInfiniteTailPackage
    (d := 1)
    tableClosedBallCouplingCutoff
    genBoundedCaseEmptySupport
    genBoundedCaseEmptySupport_saturated



theorem genBoundedCaseEmptyInfiniteTailPackage_budget_eq_zero :
    genBoundedCaseEmptyInfiniteTailPackage.tableCertifiedTotalBound = 0 := by
  rw [genBoundedCaseEmptyInfiniteTailPackage]
  rw [generatedBoundedCaseInfiniteTailPackage_tableCertifiedTotalBound_eq_card]
  simp [genBoundedCaseEmptySupport]



noncomputable def genBoundedCaseTableClosedBallRGPackage :
    @InfiniteTailTableClosedBallRGPackage Unit
      (FiniteCutoffCase 1 tableClosedBallCouplingCutoff)
      (FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff) ℕ _ _
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) 1 where
  tableWitness := genBoundedCaseEmptyInfiniteTailPackage
  closedBallRG := halfThirdScalingUnitClosedBallRGPackage
  tableBudget_le_residual := by
    rw [genBoundedCaseEmptyInfiniteTailPackage_budget_eq_zero]
    norm_num [halfThirdScalingUnitClosedBallRGPackage,
      halfThirdScalingUnitClosedBallCertificate,
      FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
      FinitePlusTailClosedBallContractionCertificate.ofResidualBound,
      halfThirdScalingCertificate_c_eq]



theorem genBoundedCaseTableClosedBallRGPackage_tailTotalTsum_le_residual :
    genBoundedCaseTableClosedBallRGPackage.tailTotalTsum ≤
      genBoundedCaseTableClosedBallRGPackage.closedBallResidual :=
  genBoundedCaseTableClosedBallRGPackage.tailTotalTsum_le_closedBallResidual



theorem genBoundedCaseTableClosedBallRGPackage_predictedExponent_eq :
    (genBoundedCaseTableClosedBallRGPackage.certificate
      FiniteWitnessPackageExample.exampleScale).predictedExponent =
        predictedNu FiniteWitnessPackageExample.exampleScale 3 :=
  genBoundedCaseTableClosedBallRGPackage.certificate_predictedExponent_eq
    FiniteWitnessPackageExample.exampleScale



noncomputable def genCubicClassEmptySupport :
    Finset (FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff) :=
  ∅


theorem genCubicClassEmptySupport_saturated :
    ∀ a,
      BoundedPolymerCase.classifyFiniteCutoffCubicClass
          tableClosedBallCouplingCutoff a ∈
          genCubicClassEmptySupport.image
            (BoundedPolymerCase.classifyFiniteCutoffCubicClass
              tableClosedBallCouplingCutoff) →
        a ∈ genCubicClassEmptySupport := by
  intro a h
  simp [genCubicClassEmptySupport] at h



noncomputable def genCubicClassEmptyInfiniteTailPackage :
    InfiniteTailTableWitnessPackage
      (Case := BoundedPolymerCase.CubicClass 1
        tableClosedBallCouplingCutoff.radius
        tableClosedBallCouplingCutoff.maxDegree
        tableClosedBallCouplingCutoff.maxRange)
      (α := FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  generatedCubicClassInfiniteTailPackage
    (d := 1)
    tableClosedBallCouplingCutoff
    genCubicClassEmptySupport
    genCubicClassEmptySupport_saturated



theorem genCubicClassEmptyInfiniteTailPackage_budget_eq_zero :
    genCubicClassEmptyInfiniteTailPackage.tableCertifiedTotalBound = 0 := by
  rw [genCubicClassEmptyInfiniteTailPackage]
  rw [generatedCubicClassInfiniteTailPackage_tableCertifiedTotalBound_eq_card]
  simp [genCubicClassEmptySupport]



noncomputable def genCubicClassTableClosedBallRGPackage :
    @InfiniteTailTableClosedBallRGPackage Unit
      (BoundedPolymerCase.CubicClass 1
        tableClosedBallCouplingCutoff.radius
        tableClosedBallCouplingCutoff.maxDegree
        tableClosedBallCouplingCutoff.maxRange)
      (FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff) ℕ _ _
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) 1 where
  tableWitness := genCubicClassEmptyInfiniteTailPackage
  closedBallRG := halfThirdScalingUnitClosedBallRGPackage
  tableBudget_le_residual := by
    rw [genCubicClassEmptyInfiniteTailPackage_budget_eq_zero]
    norm_num [halfThirdScalingUnitClosedBallRGPackage,
      halfThirdScalingUnitClosedBallCertificate,
      FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
      FinitePlusTailClosedBallContractionCertificate.ofResidualBound,
      halfThirdScalingCertificate_c_eq]



theorem genCubicClassTableClosedBallRGPackage_tailTotalTsum_le_residual :
    genCubicClassTableClosedBallRGPackage.tailTotalTsum ≤
      genCubicClassTableClosedBallRGPackage.closedBallResidual :=
  genCubicClassTableClosedBallRGPackage.tailTotalTsum_le_closedBallResidual



theorem genCubicClassTableClosedBallRGPackage_predictedExponent_eq :
    (genCubicClassTableClosedBallRGPackage.certificate
      FiniteWitnessPackageExample.exampleScale).predictedExponent =
        predictedNu FiniteWitnessPackageExample.exampleScale 3 :=
  genCubicClassTableClosedBallRGPackage.certificate_predictedExponent_eq
    FiniteWitnessPackageExample.exampleScale



noncomputable def genBoundedCaseRadiusFive :
    @InfiniteTailTableClosedBallRGPackage Unit
      (FiniteCutoffCase 1 tableClosedBallCouplingCutoff)
      (FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff) ℕ _ _
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) 1 :=
  genBoundedCaseTableClosedBallRGPackage.with_larger_closedBallRadius
    (radius' := 5)
    (by
      norm_num [genBoundedCaseTableClosedBallRGPackage,
        halfThirdScalingUnitClosedBallRGPackage,
        halfThirdScalingUnitClosedBallCertificate,
        FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
        FinitePlusTailClosedBallContractionCertificate.ofResidualBound])


theorem genBoundedCaseRadiusFive_radius_eq :
    genBoundedCaseRadiusFive.closedBallRadius = 5 :=
  rfl


theorem genBoundedCaseRadiusFive_residual_eq :
    genBoundedCaseRadiusFive.closedBallResidual = (1 : ℝ) / 2 :=
  by
    norm_num [genBoundedCaseRadiusFive,
      genBoundedCaseTableClosedBallRGPackage,
      halfThirdScalingUnitClosedBallRGPackage,
      halfThirdScalingUnitClosedBallCertificate,
      InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius,
      InfiniteTailTableClosedBallRGPackage.closedBallResidual,
      FinitePlusTailClosedBallRGPackage.with_larger_radius,
      FinitePlusTailClosedBallContractionCertificate.with_larger_radius,
      FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
      FinitePlusTailClosedBallContractionCertificate.ofResidualBound,
      halfThirdScalingCertificate_c_eq]



theorem genBoundedCaseRadiusFive_contraction_c_eq :
    genBoundedCaseRadiusFive.closedBallContraction.c = (1 : ℝ) / 2 :=
  by
    norm_num [genBoundedCaseRadiusFive,
      genBoundedCaseTableClosedBallRGPackage,
      halfThirdScalingUnitClosedBallRGPackage,
      halfThirdScalingUnitClosedBallCertificate,
      InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius,
      InfiniteTailTableClosedBallRGPackage.closedBallContraction,
      FinitePlusTailClosedBallRGPackage.with_larger_radius,
      FinitePlusTailClosedBallContractionCertificate.with_larger_radius,
      FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
      FinitePlusTailClosedBallContractionCertificate.ofResidualBound,
      halfThirdScalingCertificate_c_eq]


noncomputable def genBoundedCaseReplacedInfiniteTailPackage :
    InfiniteTailTableWitnessPackage
      (Case := FiniteCutoffCase 1 tableClosedBallCouplingCutoff)
      (α := FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope
    (d := 1)
    tableClosedBallCouplingCutoff
    genBoundedCaseEmptySupport
    genBoundedCaseEmptySupport_saturated



theorem genBoundedCaseReplacedInfiniteTailPackage_budget_eq_two :
    genBoundedCaseReplacedInfiniteTailPackage.tableCertifiedTotalBound =
      2 := by
  rw [genBoundedCaseReplacedInfiniteTailPackage]
  rw [
    generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two]
  simp [genBoundedCaseEmptySupport]



noncomputable def genBoundedCaseReplacedPackage :
    @InfiniteTailTableClosedBallRGPackage Unit
      (FiniteCutoffCase 1 tableClosedBallCouplingCutoff)
      (FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff) ℕ _ _
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) 1 :=
  genBoundedCaseRadiusFive.with_tableWitness_as_closedBallResidual
    genBoundedCaseReplacedInfiniteTailPackage
    (by
      rw [genBoundedCaseRadiusFive_residual_eq,
        genBoundedCaseReplacedInfiniteTailPackage_budget_eq_two]
      norm_num)
    (by
      rw [genBoundedCaseReplacedInfiniteTailPackage_budget_eq_two,
        genBoundedCaseRadiusFive_contraction_c_eq,
        genBoundedCaseRadiusFive_radius_eq]
      norm_num)



theorem genBoundedCaseReplacedPackage_residual_eq_two :
    genBoundedCaseReplacedPackage.closedBallResidual = 2 := by
  rw [genBoundedCaseReplacedPackage]
  rw [with_tableWitness_as_closedBallResidual_closedBallResidual]
  exact genBoundedCaseReplacedInfiniteTailPackage_budget_eq_two


theorem genBoundedCaseReplacedPackage_thermal_eq :
    genBoundedCaseReplacedPackage.closedBallRG.thermal = 3 :=
  rfl


theorem genBoundedCaseReplacedPackage_radius_eq :
    genBoundedCaseReplacedPackage.closedBallRadius = 5 := by
  rw [genBoundedCaseReplacedPackage]
  rw [with_tableWitness_as_closedBallResidual_closedBallRadius]
  exact genBoundedCaseRadiusFive_radius_eq



theorem genBoundedCaseReplacedPackage_contraction_c_eq :
    genBoundedCaseReplacedPackage.closedBallContraction.c = (1 : ℝ) / 2 := by
  rw [genBoundedCaseReplacedPackage]
  rw [with_tableWitness_as_closedBallResidual_closedBallContraction]
  exact genBoundedCaseRadiusFive_contraction_c_eq


theorem genBoundedCaseReplacedPackage_budget_eq_two :
    genBoundedCaseReplacedPackage.tableCertifiedTotalBound = 2 := by
  rw [genBoundedCaseReplacedPackage]
  rw [with_tableWitness_as_closedBallResidual_tableCertifiedTotalBound]
  exact genBoundedCaseReplacedInfiniteTailPackage_budget_eq_two



theorem genBoundedCaseReplacedPackage_budget_eq_residual :
    genBoundedCaseReplacedPackage.tableCertifiedTotalBound =
      genBoundedCaseReplacedPackage.closedBallResidual := by
  rw [genBoundedCaseReplacedPackage_budget_eq_two,
    genBoundedCaseReplacedPackage_residual_eq_two]



theorem genBoundedCaseReplacedPackage_tailTotalTsum_le_residual :
    genBoundedCaseReplacedPackage.tailTotalTsum ≤
      genBoundedCaseReplacedPackage.closedBallResidual :=
  genBoundedCaseReplacedPackage.tailTotalTsum_le_closedBallResidual



theorem genBoundedCaseReplacedPackage_tailTotalTsum_radius :
    genBoundedCaseReplacedPackage.tailTotalTsum +
        genBoundedCaseReplacedPackage.closedBallContraction.c *
      genBoundedCaseReplacedPackage.closedBallRadius ≤
      genBoundedCaseReplacedPackage.closedBallRadius :=
  InfiniteTailTableClosedBallRGPackage.tailTotalTsum_plus_mul_radius_le_radius
    genBoundedCaseReplacedPackage



@[simp] theorem genBoundedCaseReplacedPackage_certificate_eq
    (scale : BlockScale) :
    genBoundedCaseReplacedPackage.certificate scale =
      genBoundedCaseRadiusFive.certificate scale :=
  rfl



theorem genBoundedCaseReplacedPackage_predictedExponent_eq :
    (genBoundedCaseReplacedPackage.certificate
      FiniteWitnessPackageExample.exampleScale).predictedExponent =
        predictedNu FiniteWitnessPackageExample.exampleScale 3 :=
  by
    simpa using
      InfiniteTailTableClosedBallRGPackage.certificate_predictedExponent_eq
        genBoundedCaseReplacedPackage
        FiniteWitnessPackageExample.exampleScale



noncomputable def genCubicClassRadiusFive :
    @InfiniteTailTableClosedBallRGPackage Unit
      (BoundedPolymerCase.CubicClass 1
        tableClosedBallCouplingCutoff.radius
        tableClosedBallCouplingCutoff.maxDegree
        tableClosedBallCouplingCutoff.maxRange)
      (FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff) ℕ _ _
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) 1 :=
  genCubicClassTableClosedBallRGPackage.with_larger_closedBallRadius
    (radius' := 5)
    (by
      norm_num [genCubicClassTableClosedBallRGPackage,
        halfThirdScalingUnitClosedBallRGPackage,
        halfThirdScalingUnitClosedBallCertificate,
        FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
        FinitePlusTailClosedBallContractionCertificate.ofResidualBound])


theorem genCubicClassRadiusFive_radius_eq :
    genCubicClassRadiusFive.closedBallRadius = 5 :=
  rfl


theorem genCubicClassRadiusFive_residual_eq :
    genCubicClassRadiusFive.closedBallResidual = (1 : ℝ) / 2 :=
  by
    norm_num [genCubicClassRadiusFive,
      genCubicClassTableClosedBallRGPackage,
      halfThirdScalingUnitClosedBallRGPackage,
      halfThirdScalingUnitClosedBallCertificate,
      InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius,
      InfiniteTailTableClosedBallRGPackage.closedBallResidual,
      FinitePlusTailClosedBallRGPackage.with_larger_radius,
      FinitePlusTailClosedBallContractionCertificate.with_larger_radius,
      FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
      FinitePlusTailClosedBallContractionCertificate.ofResidualBound,
      halfThirdScalingCertificate_c_eq]


theorem genCubicClassRadiusFive_contraction_c_eq :
    genCubicClassRadiusFive.closedBallContraction.c = (1 : ℝ) / 2 :=
  by
    norm_num [genCubicClassRadiusFive,
      genCubicClassTableClosedBallRGPackage,
      halfThirdScalingUnitClosedBallRGPackage,
      halfThirdScalingUnitClosedBallCertificate,
      InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius,
      InfiniteTailTableClosedBallRGPackage.closedBallContraction,
      FinitePlusTailClosedBallRGPackage.with_larger_radius,
      FinitePlusTailClosedBallContractionCertificate.with_larger_radius,
      FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
      FinitePlusTailClosedBallContractionCertificate.ofResidualBound,
      halfThirdScalingCertificate_c_eq]


noncomputable def genCubicClassReplacedInfiniteTailPackage :
    InfiniteTailTableWitnessPackage
      (Case := BoundedPolymerCase.CubicClass 1
        tableClosedBallCouplingCutoff.radius
        tableClosedBallCouplingCutoff.maxDegree
        tableClosedBallCouplingCutoff.maxRange)
      (α := FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  generatedCubicClassInfiniteTailPackage_replacedTailEnvelope
    (d := 1)
    tableClosedBallCouplingCutoff
    genCubicClassEmptySupport
    genCubicClassEmptySupport_saturated



theorem genCubicClassReplacedInfiniteTailPackage_budget_eq_two :
    genCubicClassReplacedInfiniteTailPackage.tableCertifiedTotalBound =
      2 := by
  rw [genCubicClassReplacedInfiniteTailPackage]
  rw [
    generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two]
  simp [genCubicClassEmptySupport]



noncomputable def genCubicClassReplacedPackage :
    @InfiniteTailTableClosedBallRGPackage Unit
      (BoundedPolymerCase.CubicClass 1
        tableClosedBallCouplingCutoff.radius
        tableClosedBallCouplingCutoff.maxDegree
        tableClosedBallCouplingCutoff.maxRange)
      (FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff) ℕ _ _
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) 1 :=
  genCubicClassRadiusFive.with_tableWitness_as_closedBallResidual
    genCubicClassReplacedInfiniteTailPackage
    (by
      rw [genCubicClassRadiusFive_residual_eq,
        genCubicClassReplacedInfiniteTailPackage_budget_eq_two]
      norm_num)
    (by
      rw [genCubicClassReplacedInfiniteTailPackage_budget_eq_two,
        genCubicClassRadiusFive_contraction_c_eq,
        genCubicClassRadiusFive_radius_eq]
      norm_num)



theorem genCubicClassReplacedPackage_residual_eq_two :
    genCubicClassReplacedPackage.closedBallResidual = 2 := by
  rw [genCubicClassReplacedPackage]
  rw [with_tableWitness_as_closedBallResidual_closedBallResidual]
  exact genCubicClassReplacedInfiniteTailPackage_budget_eq_two


theorem genCubicClassReplacedPackage_thermal_eq :
    genCubicClassReplacedPackage.closedBallRG.thermal = 3 :=
  rfl


theorem genCubicClassReplacedPackage_radius_eq :
    genCubicClassReplacedPackage.closedBallRadius = 5 := by
  rw [genCubicClassReplacedPackage]
  rw [with_tableWitness_as_closedBallResidual_closedBallRadius]
  exact genCubicClassRadiusFive_radius_eq


theorem genCubicClassReplacedPackage_contraction_c_eq :
    genCubicClassReplacedPackage.closedBallContraction.c = (1 : ℝ) / 2 := by
  rw [genCubicClassReplacedPackage]
  rw [with_tableWitness_as_closedBallResidual_closedBallContraction]
  exact genCubicClassRadiusFive_contraction_c_eq


theorem genCubicClassReplacedPackage_budget_eq_two :
    genCubicClassReplacedPackage.tableCertifiedTotalBound = 2 := by
  rw [genCubicClassReplacedPackage]
  rw [with_tableWitness_as_closedBallResidual_tableCertifiedTotalBound]
  exact genCubicClassReplacedInfiniteTailPackage_budget_eq_two



theorem genCubicClassReplacedPackage_budget_eq_residual :
    genCubicClassReplacedPackage.tableCertifiedTotalBound =
      genCubicClassReplacedPackage.closedBallResidual := by
  rw [genCubicClassReplacedPackage_budget_eq_two,
    genCubicClassReplacedPackage_residual_eq_two]



theorem genCubicClassReplacedPackage_tailTotalTsum_le_residual :
    genCubicClassReplacedPackage.tailTotalTsum ≤
      genCubicClassReplacedPackage.closedBallResidual :=
  genCubicClassReplacedPackage.tailTotalTsum_le_closedBallResidual



theorem genCubicClassReplacedPackage_tailTotalTsum_radius :
    genCubicClassReplacedPackage.tailTotalTsum +
        genCubicClassReplacedPackage.closedBallContraction.c *
      genCubicClassReplacedPackage.closedBallRadius ≤
      genCubicClassReplacedPackage.closedBallRadius :=
  InfiniteTailTableClosedBallRGPackage.tailTotalTsum_plus_mul_radius_le_radius
    genCubicClassReplacedPackage



@[simp] theorem genCubicClassReplacedPackage_certificate_eq
    (scale : BlockScale) :
    genCubicClassReplacedPackage.certificate scale =
      genCubicClassRadiusFive.certificate scale :=
  rfl



theorem genCubicClassReplacedPackage_predictedExponent_eq :
    (genCubicClassReplacedPackage.certificate
      FiniteWitnessPackageExample.exampleScale).predictedExponent =
        predictedNu FiniteWitnessPackageExample.exampleScale 3 :=
  by
    simpa using
      InfiniteTailTableClosedBallRGPackage.certificate_predictedExponent_eq
        genCubicClassReplacedPackage
        FiniteWitnessPackageExample.exampleScale



noncomputable def halfThirdScalingUnitClosedBallRGCertificate :
    RGCertificate halfThirdScalingModel :=
  halfThirdScalingUnitClosedBallRGPackage.certificate
    halfThirdScalingBlockScale halfThirdScalingModel



theorem halfThirdScalingUnitClosedBallRGCertificate_fixedPointEnclosure :
    halfThirdScalingUnitClosedBallRGCertificate.FixedPointEnclosure := by
  simpa [halfThirdScalingUnitClosedBallRGCertificate] using
    halfThirdScalingUnitClosedBallCertificate.certificate_fixedPointEnclosure
      halfThirdScalingBlockScale halfThirdScalingModel 3 (by norm_num)



theorem halfThirdScalingUnitClosedBallRGPackage_thermalEigenvalue_eq :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).thermalEigenvalue =
        3 :=
  halfThirdScalingUnitClosedBallRGPackage.certificate_thermalEigenvalue_eq
    halfThirdScalingBlockScale halfThirdScalingModel



theorem halfThirdScalingUnitClosedBallRGPackage_scale_eq :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).scale =
        halfThirdScalingBlockScale :=
  halfThirdScalingUnitClosedBallRGPackage.certificate_scale_eq
    halfThirdScalingBlockScale halfThirdScalingModel



theorem halfThirdScalingUnitClosedBallRGPackage_predictedExponent_eq :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent =
        predictedNu halfThirdScalingBlockScale 3 :=
  halfThirdScalingUnitClosedBallRGPackage.certificate_predictedExponent_eq
    halfThirdScalingBlockScale halfThirdScalingModel



theorem halfThirdScalingUnitClosedBallRGCertificate_fixedPoint_mem :
    FinitePlusTailState.ClosedBall unitCenterState 1
      halfThirdScalingUnitClosedBallRGCertificate.fixedPointData.fixedPoint := by
  simpa [halfThirdScalingUnitClosedBallRGCertificate,
    halfThirdScalingUnitClosedBallCertificate] using
    halfThirdScalingUnitClosedBallCertificate.certificate_fixedPoint_mem_closedBall
      halfThirdScalingBlockScale halfThirdScalingModel 3 (by norm_num)



theorem halfThirdScalingUnitClosedBallRGCertificate_valid_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      halfThirdScalingUnitClosedBallRGCertificate.RGToExponentBridge
        correlationLength) :
    halfThirdScalingUnitClosedBallRGCertificate.Valid correlationLength := by
  simpa [halfThirdScalingUnitClosedBallRGCertificate] using
    halfThirdScalingUnitClosedBallCertificate.certificate_valid_of_bridge
      halfThirdScalingBlockScale halfThirdScalingModel 3 (by norm_num)
      correlationLength hbridge



theorem halfThirdScalingUnitClosedBallRGCertificate_hasCriticalNu_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      halfThirdScalingUnitClosedBallRGCertificate.RGToExponentBridge
        correlationLength) :
    HasCriticalNu halfThirdScalingModel correlationLength
      halfThirdScalingUnitClosedBallRGCertificate.predictedExponent :=
  (halfThirdScalingUnitClosedBallRGCertificate_valid_of_bridge
    correlationLength hbridge).hasCriticalNu



theorem
    halfThirdScalingUnitClosedBallRGCertificate_rgToExponentBridge_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu halfThirdScalingModel correlationLength
        halfThirdScalingUnitClosedBallRGCertificate.predictedExponent) :
    halfThirdScalingUnitClosedBallRGCertificate.RGToExponentBridge
      correlationLength := by
  simpa [halfThirdScalingUnitClosedBallRGCertificate] using
    FinitePlusTailClosedBallContractionCertificate.certificate_rgToExponentBridge_of_hasCriticalNu
      halfThirdScalingUnitClosedBallCertificate
      halfThirdScalingBlockScale halfThirdScalingModel 3 (by norm_num)
      correlationLength hν



theorem halfThirdScalingUnitClosedBallRGCertificate_valid_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu halfThirdScalingModel correlationLength
        halfThirdScalingUnitClosedBallRGCertificate.predictedExponent) :
    halfThirdScalingUnitClosedBallRGCertificate.Valid correlationLength := by
  simpa [halfThirdScalingUnitClosedBallRGCertificate] using
    halfThirdScalingUnitClosedBallCertificate.certificate_valid_of_hasCriticalNu
      halfThirdScalingBlockScale halfThirdScalingModel 3 (by norm_num)
      correlationLength hν



theorem halfThirdScalingUnitClosedBallRGPackage_valid_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
        correlationLength) :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      correlationLength :=
  halfThirdScalingUnitClosedBallRGPackage.certificate_valid_of_bridge
    halfThirdScalingBlockScale halfThirdScalingModel correlationLength hbridge



theorem halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
        correlationLength) :
    HasCriticalNu halfThirdScalingModel correlationLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent :=
  halfThirdScalingUnitClosedBallRGPackage.certificate_hasCriticalNu_of_bridge
    halfThirdScalingBlockScale halfThirdScalingModel correlationLength hbridge



theorem halfThirdScalingUnitClosedBallRGPackage_rgToExponentBridge_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu halfThirdScalingModel correlationLength
        (halfThirdScalingUnitClosedBallRGPackage.certificate
          halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent) :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      correlationLength :=
  FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_hasCriticalNu
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale halfThirdScalingModel correlationLength hν



theorem halfThirdScalingUnitClosedBallRGPackage_valid_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu halfThirdScalingModel correlationLength
        (halfThirdScalingUnitClosedBallRGPackage.certificate
          halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent) :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      correlationLength :=
  halfThirdScalingUnitClosedBallRGPackage.certificate_valid_of_hasCriticalNu
    halfThirdScalingBlockScale halfThirdScalingModel correlationLength hν


theorem halfThirdScalingClosedBallCertificate_mapsClosedBall {radius : ℝ}
    (hradius : 0 ≤ radius) :
    FinitePlusTailState.MapsClosedBall
      halfThirdScalingCertificate.map zeroState radius := by
  simpa [halfThirdScalingClosedBallCertificate] using
    (halfThirdScalingClosedBallCertificate hradius).mapsClosedBall



theorem halfThirdScalingClosedBallCertificate_fixedPoint_mem {radius : ℝ}
    (hradius : 0 ≤ radius) :
    FinitePlusTailState.ClosedBall zeroState radius
      halfThirdScalingCertificate.fixedPoint := by
  simpa [halfThirdScalingClosedBallCertificate,
    FinitePlusTailClosedBallContractionCertificate.fixedPoint] using
    (halfThirdScalingClosedBallCertificate hradius).fixedPoint_mem


theorem halfThirdScalingClosedBallCertificate_exists_fixedPoint {radius : ℝ}
    (hradius : 0 ≤ radius) :
    ∃ p : FinitePlusTailState 1 ℕ,
      halfThirdScalingCertificate.map p = p ∧
        FinitePlusTailState.ClosedBall zeroState radius p := by
  simpa [halfThirdScalingClosedBallCertificate,
    FinitePlusTailClosedBallContractionCertificate.fixedPoint] using
    (halfThirdScalingClosedBallCertificate hradius).exists_fixedPoint


theorem halfThirdScalingCertificate_iterate_contracts
    (k : ℕ) (x y : FinitePlusTailState 1 ℕ) :
    (halfThirdScalingCertificate.iterate k x).dist
        (halfThirdScalingCertificate.iterate k y) ≤
      ((1 : ℝ) / 2) ^ k * x.dist y := by
  simpa [halfThirdScalingCertificate_c_eq] using
    halfThirdScalingCertificate.iterate_contracts k x y


theorem halfThirdScalingCertificate_iterate_contracts_to_fixedPoint
    (k : ℕ) (x : FinitePlusTailState 1 ℕ) :
    (halfThirdScalingCertificate.iterate k x).dist
        halfThirdScalingCertificate.fixedPoint ≤
      ((1 : ℝ) / 2) ^ k *
        x.dist halfThirdScalingCertificate.fixedPoint := by
  simpa [halfThirdScalingCertificate_c_eq] using
    halfThirdScalingCertificate.iterate_dist_le_pow_mul_fixedPoint x k



theorem halfThirdScalingCertificate_iterate_mem_zero_closedBall
    {radius : ℝ} (hradius : 0 ≤ radius)
    {x : FinitePlusTailState 1 ℕ}
    (hx : FinitePlusTailState.ClosedBall zeroState radius x) (k : ℕ) :
    FinitePlusTailState.ClosedBall zeroState radius
      (halfThirdScalingCertificate.iterate k x) :=
  halfThirdScalingCertificate.mapsClosedBall_iterate_mem
    (halfThirdScalingCertificate_mapsClosedBall_zero hradius) hx k



theorem halfThirdScalingClosedBallCertificate_iterate_mem
    {radius : ℝ} (hradius : 0 ≤ radius)
    {x : FinitePlusTailState 1 ℕ}
    (hx : FinitePlusTailState.ClosedBall zeroState radius x) (k : ℕ) :
    FinitePlusTailState.ClosedBall zeroState radius
      (halfThirdScalingCertificate.iterate k x) := by
  simpa [halfThirdScalingClosedBallCertificate] using
    (halfThirdScalingClosedBallCertificate hradius).iterate_mem hx k


theorem halfThirdScalingClosedBallCertificate_fixedPoint_mem_larger
    {radius radius' : ℝ} (hradius : 0 ≤ radius)
    (hle : radius ≤ radius') :
    FinitePlusTailState.ClosedBall zeroState radius'
      halfThirdScalingCertificate.fixedPoint := by
  simpa [halfThirdScalingClosedBallCertificate,
    FinitePlusTailClosedBallContractionCertificate.fixedPoint] using
    ((halfThirdScalingClosedBallCertificate hradius).with_larger_radius hle).fixedPoint_mem



theorem halfThirdScalingRadiusOneFromZero_fixedPoint_mem :
    FinitePlusTailState.ClosedBall zeroState 1
      halfThirdScalingCertificate.fixedPoint := by
  simpa [halfThirdScalingRadiusOneFromZeroClosedBallCertificate,
    halfThirdScalingRadiusZeroClosedBallCertificate,
    halfThirdScalingClosedBallCertificate,
    FinitePlusTailClosedBallContractionCertificate.fixedPoint] using
    halfThirdScalingRadiusOneFromZeroClosedBallCertificate.fixedPoint_mem



theorem halfThirdScalingUnitClosedBallCertificate_fixedPoint_mem :
    FinitePlusTailState.ClosedBall unitCenterState 1
      halfThirdScalingCertificate.fixedPoint := by
  simpa [halfThirdScalingUnitClosedBallCertificate,
    FinitePlusTailClosedBallContractionCertificate.fixedPoint] using
    halfThirdScalingUnitClosedBallCertificate.fixedPoint_mem



noncomputable def tailHalfMap (x : FinitePlusTailState 1 ℕ) : SummableTail ℕ :=
  SummableTail.scale ((1 : ℝ) / 2) x.tail




noncomputable def zeroFiniteBlockTailHalfCertificate :
    FinitePlusTailLipschitzCertificate 1 ℕ :=
  FinitePlusTailLipschitzCertificate.ofColumnSumFiniteBlock
    FiniteContraction.ZeroLinearExample.columnSumContraction
    FiniteContraction.ZeroLinearExample.matrix_mem_intervals
    tailHalfMap
    (finiteToTail := 0)
    (tailToTail := (1 : ℝ) / 2)
    (c := (1 : ℝ) / 2)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by
      norm_num [FiniteContraction.ZeroLinearExample.columnSumContraction])
    (by norm_num)
    (by
      intro x y
      simpa [tailHalfMap, FinitePlusTailState.tailDist] using
        le_of_eq (SummableTail.dist_scale ((1 : ℝ) / 2) x.tail y.tail))


theorem zeroFiniteBlockTailHalfCertificate_c_eq :
    zeroFiniteBlockTailHalfCertificate.c = (1 : ℝ) / 2 := by
  rfl



theorem zeroFiniteBlockTailHalfCertificate_mixed_lipschitz
    (x y : FinitePlusTailState 1 ℕ) :
    (zeroFiniteBlockTailHalfCertificate.map x).dist
        (zeroFiniteBlockTailHalfCertificate.map y) ≤
      ((1 : ℝ) / 2) * x.dist y := by
  simpa [zeroFiniteBlockTailHalfCertificate_c_eq] using
    zeroFiniteBlockTailHalfCertificate.mixed_lipschitz x y


theorem zeroFiniteBlockTailHalfCertificate_map_zero :
    zeroFiniteBlockTailHalfCertificate.map zeroState = zeroState := by
  ext i <;>
    simp [zeroFiniteBlockTailHalfCertificate,
      FinitePlusTailLipschitzCertificate.ofColumnSumFiniteBlock,
      FiniteContraction.ZeroLinearExample.matrix, RatInterval.matVec,
      zeroState, tailHalfMap, SummableTail.scale]


noncomputable def zeroFiniteBlockTailHalfClosedBallCertificate {radius : ℝ}
    (hradius : 0 ≤ radius) :
    FinitePlusTailClosedBallContractionCertificate 1 ℕ :=
  FinitePlusTailClosedBallContractionCertificate.ofFixedCenter
    zeroFiniteBlockTailHalfCertificate zeroState hradius
    zeroFiniteBlockTailHalfCertificate_map_zero



theorem zeroFiniteBlockTailHalfClosedBallCertificate_exists_fixedPoint
    {radius : ℝ} (hradius : 0 ≤ radius) :
    ∃ p : FinitePlusTailState 1 ℕ,
      zeroFiniteBlockTailHalfCertificate.map p = p ∧
        FinitePlusTailState.ClosedBall zeroState radius p := by
  simpa [zeroFiniteBlockTailHalfClosedBallCertificate,
    FinitePlusTailClosedBallContractionCertificate.fixedPoint] using
    (zeroFiniteBlockTailHalfClosedBallCertificate hradius).exists_fixedPoint

end FinitePlusTailContractionExample

end Exact3D
end StatMech

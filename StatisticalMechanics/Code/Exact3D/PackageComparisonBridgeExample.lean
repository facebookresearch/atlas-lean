/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.PackageComparisonBridge
import Code.Exact3D.FiniteWitnessPackageExample
import Code.Exact3D.FinitePlusTailContractionExample
import Code.Exact3D.InfiniteTailWitnessPackageExample











namespace StatMech
namespace Exact3D
namespace PackageComparisonBridgeExample

open FiniteWitnessPackageExample
open FinitePlusTailContractionExample
open InfiniteTailWitnessPackageExample


noncomputable def doubledHierarchicalCorrelationLength (β : ℝ) : ℝ :=
  2 * hierarchicalCorrelationLength β


theorem hierarchicalCorrelationLength_eventually_pos :
    ∀ᶠ β in nhdsWithin HierarchicalModel.betaC (Set.Iio HierarchicalModel.betaC),
      0 < hierarchicalCorrelationLength β :=
  Filter.Eventually.of_forall fun _ => Real.exp_pos _



theorem doubledHierarchicalCorrelationLength_comparable :
    ∀ᶠ β in nhdsWithin HierarchicalModel.betaC (Set.Iio HierarchicalModel.betaC),
      (2 : ℝ) * hierarchicalCorrelationLength β ≤
          doubledHierarchicalCorrelationLength β ∧
        doubledHierarchicalCorrelationLength β ≤
          (2 : ℝ) * hierarchicalCorrelationLength β :=
  Filter.Eventually.of_forall fun _ => by
    simp [doubledHierarchicalCorrelationLength]



theorem hierarchicalWitnessBridge :
    hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge
      hierarchicalCorrelationLength := by
  change HasCriticalNu HierarchicalModel hierarchicalCorrelationLength
    hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent
  simpa [hierarchicalContributionSplitWitnessPackage_predictedExponent_eq,
    hierarchicalNu, hierarchicalCertificate, predictedNu] using
    hierarchical_hasCriticalNu



theorem hierarchicalWitnessBridge_doubled_by_package_comparison :
    hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge
      doubledHierarchicalCorrelationLength :=
  hierarchicalContributionSplitWitnessPackage
    |>.rgToExponentBridge_of_eventually_const_mul_le_le
        hierarchicalWitnessBridge
        hierarchicalCorrelationLength_eventually_pos
        (by norm_num : (0 : ℝ) < 2)
        (by norm_num : (0 : ℝ) < 2)
        doubledHierarchicalCorrelationLength_comparable



theorem hierarchicalWitness_valid_doubled_by_package_comparison :
    hierarchicalContributionSplitWitnessPackage.certificate.Valid
      doubledHierarchicalCorrelationLength :=
  hierarchicalContributionSplitWitnessPackage.valid_of_eventually_const_mul_le_le
    hierarchicalWitnessBridge
    hierarchicalCorrelationLength_eventually_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    doubledHierarchicalCorrelationLength_comparable



theorem hierarchicalWitness_hasCriticalNu_doubled_by_package_comparison :
    HasCriticalNu HierarchicalModel doubledHierarchicalCorrelationLength
      hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent :=
  hierarchicalContributionSplitWitnessPackage.hasCriticalNu_of_eventually_const_mul_le_le
    hierarchicalWitnessBridge
    hierarchicalCorrelationLength_eventually_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    doubledHierarchicalCorrelationLength_comparable



theorem halfThirdScalingHyperbolicSplitting_bridge_doubled_by_package_comparison :
    halfThirdScalingRGCertificate.RGToExponentBridge
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) := by
  let H := halfThirdScalingHyperbolicSplitting
  simpa [halfThirdScalingRGCertificate] using
    H.certificate_rgToExponentBridge_of_eventually_const_mul_le_le
      halfThirdScalingBlockScale
      halfThirdScalingModel
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem halfThirdScalingHyperbolicSplitting_valid_doubled_by_package_comparison :
    halfThirdScalingRGCertificate.Valid
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) := by
  simpa [halfThirdScalingRGCertificate] using
    halfThirdScalingHyperbolicSplitting.certificate_valid_of_eventually_const_mul_le_le
      halfThirdScalingBlockScale
      halfThirdScalingModel
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem halfThirdScalingHyperbolicSplitting_hasCriticalNu_doubled_by_package_comparison :
    HasCriticalNu halfThirdScalingModel
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β)
      halfThirdScalingRGCertificate.predictedExponent := by
  simpa [halfThirdScalingRGCertificate] using
    halfThirdScalingHyperbolicSplitting.certificate_hasCriticalNu_of_eventually_const_mul_le_le
      halfThirdScalingBlockScale
      halfThirdScalingModel
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem halfThirdScalingHyperbolicSplitting_bridge_doubled_by_package_prefactor :
    halfThirdScalingRGCertificate.RGToExponentBridge
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) := by
  let H := halfThirdScalingHyperbolicSplitting
  simpa [halfThirdScalingRGCertificate] using
    H.certificate_rgToExponentBridge_mul_log_negligible_prefactor
      halfThirdScalingBlockScale
      halfThirdScalingModel
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      halfThirdScalingCorrelationLength_pos
      halfThirdScalingDoublePrefactor_pos
      halfThirdScalingDoublePrefactor_log_negligible



theorem halfThirdScalingHyperbolicSplitting_valid_doubled_by_package_prefactor :
    halfThirdScalingRGCertificate.Valid
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) := by
  simpa [halfThirdScalingRGCertificate] using
    halfThirdScalingHyperbolicSplitting.certificate_valid_mul_log_negligible_prefactor
      halfThirdScalingBlockScale
      halfThirdScalingModel
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      halfThirdScalingCorrelationLength_pos
      halfThirdScalingDoublePrefactor_pos
      halfThirdScalingDoublePrefactor_log_negligible


theorem halfThirdScalingHyperbolicSplitting_hasCriticalNu_doubled_by_package_prefactor :
    HasCriticalNu halfThirdScalingModel
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β)
      halfThirdScalingRGCertificate.predictedExponent := by
  simpa [halfThirdScalingRGCertificate] using
    halfThirdScalingHyperbolicSplitting.certificate_hasCriticalNu_mul_log_negligible_prefactor
      halfThirdScalingBlockScale
      halfThirdScalingModel
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      halfThirdScalingCorrelationLength_pos
      halfThirdScalingDoublePrefactor_pos
      halfThirdScalingDoublePrefactor_log_negligible



theorem halfThirdScalingBlockRGPackage_bridge_doubled_by_package_comparison :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  halfThirdScalingBlockRGPackage
    |>.certificate_rgToExponentBridge_of_eventually_const_mul_le_le
      halfThirdScalingBlockScale
      halfThirdScalingModel
      (by
        simpa [halfThirdScalingBlockRGCertificate] using
          halfThirdScalingBlockRGCertificate_bridge_from_prefactorInputs)
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem halfThirdScalingBlockRGPackage_valid_doubled_by_package_comparison :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  halfThirdScalingBlockRGPackage.certificate_valid_of_eventually_const_mul_le_le
    halfThirdScalingBlockScale
    halfThirdScalingModel
    (by
      simpa [halfThirdScalingBlockRGCertificate] using
        halfThirdScalingBlockRGCertificate_bridge_from_prefactorInputs)
    halfThirdScalingCorrelationLength_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    halfThirdScalingDoubleComparison



theorem
    halfThirdScalingBlockRGPackage_hasCriticalNu_doubled_by_package_comparison :
    HasCriticalNu halfThirdScalingModel
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β)
      (halfThirdScalingBlockRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent :=
  FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_eventually_const_mul_le_le
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    (by
      simpa [halfThirdScalingBlockRGCertificate] using
        halfThirdScalingBlockRGCertificate_bridge_from_prefactorInputs)
    halfThirdScalingCorrelationLength_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    halfThirdScalingDoubleComparison



theorem halfThirdScalingUnitClosedBallRGPackage_bridge_doubled_by_package_comparison :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  halfThirdScalingUnitClosedBallRGPackage
    |>.certificate_rgToExponentBridge_of_eventually_const_mul_le_le
      halfThirdScalingBlockScale
      halfThirdScalingModel
      (by
        apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
        exact halfThirdScalingCorrelationLength_exact_power)
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem
    halfThirdScalingUnitClosedBallRGPackage_valid_doubled_by_package_comparison :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  FinitePlusTailClosedBallRGPackage.certificate_valid_of_eventually_const_mul_le_le
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    (by
      apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
      exact halfThirdScalingCorrelationLength_exact_power)
    halfThirdScalingCorrelationLength_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    halfThirdScalingDoubleComparison



theorem
    halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_doubled_by_package_comparison :
    HasCriticalNu halfThirdScalingModel
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β)
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent :=
  FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_const_mul_le_le
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    (by
      apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
      exact halfThirdScalingCorrelationLength_exact_power)
    halfThirdScalingCorrelationLength_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    halfThirdScalingDoubleComparison



theorem zeroTableClosedBallRGPackage_bridge_doubled_by_package_comparison :
    (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  zeroTableClosedBallRGPackage
    |>.certificate_rgToExponentBridge_of_eventually_const_mul_le_le
      exampleScale
      (by
        apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
        exact halfThirdScalingCorrelationLength_exact_power)
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem zeroTableClosedBallRGPackage_valid_doubled_by_package_comparison :
    (zeroTableClosedBallRGPackage.certificate exampleScale).Valid
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  InfiniteTailTableClosedBallRGPackage.certificate_valid_of_eventually_const_mul_le_le
    zeroTableClosedBallRGPackage
    exampleScale
    (by
      apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
      exact halfThirdScalingCorrelationLength_exact_power)
    halfThirdScalingCorrelationLength_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    halfThirdScalingDoubleComparison



theorem
    zeroTableClosedBallRGPackage_hasCriticalNu_doubled_by_package_comparison :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β)
      (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent :=
  InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_const_mul_le_le
    zeroTableClosedBallRGPackage
    exampleScale
    (by
      apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
      exact halfThirdScalingCorrelationLength_exact_power)
    halfThirdScalingCorrelationLength_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    halfThirdScalingDoubleComparison



theorem
    zeroTableClosedBallRGPackage_bridge_doubled_by_package_comparison_congr_predictedExponent :
    (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  zeroTableClosedBallRGPackage
    |>.certificate_rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
      exampleScale
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      (by
        rw [zeroTableClosedBallRGPackage_predictedExponent_eq]
        simpa [predictedNu, BlockScale.toReal, exampleScale,
          halfThirdScalingBlockScale] using
          halfThirdScalingRGCertificate_predictedExponent_eq.symm)
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem
    zeroTableClosedBallRGPackage_valid_doubled_by_package_comparison_congr_predictedExponent :
    (zeroTableClosedBallRGPackage.certificate exampleScale).Valid
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  zeroTableClosedBallRGPackage
    |>.certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent
      exampleScale
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      (by
        rw [zeroTableClosedBallRGPackage_predictedExponent_eq]
        simpa [predictedNu, BlockScale.toReal, exampleScale,
          halfThirdScalingBlockScale] using
          halfThirdScalingRGCertificate_predictedExponent_eq.symm)
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem
    zeroTableClosedBallRGPackage_hasCriticalNu_doubled_by_package_comparison_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β)
      (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent :=
  zeroTableClosedBallRGPackage
    |>.certificate_hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent
      exampleScale
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      (by
        rw [zeroTableClosedBallRGPackage_predictedExponent_eq]
        simpa [predictedNu, BlockScale.toReal, exampleScale,
          halfThirdScalingBlockScale] using
          halfThirdScalingRGCertificate_predictedExponent_eq.symm)
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem zeroTableClosedBallRGPackage_bridge_doubled_by_package_prefactor :
    (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  zeroTableClosedBallRGPackage
    |>.certificate_rgToExponentBridge_mul_log_negligible_prefactor
      exampleScale
      (by
        apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
        exact halfThirdScalingCorrelationLength_exact_power)
      halfThirdScalingCorrelationLength_pos
      halfThirdScalingDoublePrefactor_pos
      halfThirdScalingDoublePrefactor_log_negligible



theorem zeroTableClosedBallRGPackage_valid_doubled_by_package_prefactor :
    (zeroTableClosedBallRGPackage.certificate exampleScale).Valid
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  InfiniteTailTableClosedBallRGPackage.certificate_valid_mul_log_negligible_prefactor
    zeroTableClosedBallRGPackage
    exampleScale
    (by
      apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
      exact halfThirdScalingCorrelationLength_exact_power)
    halfThirdScalingCorrelationLength_pos
    halfThirdScalingDoublePrefactor_pos
    halfThirdScalingDoublePrefactor_log_negligible



theorem zeroTableClosedBallRGPackage_hasCriticalNu_doubled_by_package_prefactor :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β)
      (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent :=
  InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_mul_log_negligible_prefactor
    zeroTableClosedBallRGPackage
    exampleScale
    (by
      apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
      exact halfThirdScalingCorrelationLength_exact_power)
    halfThirdScalingCorrelationLength_pos
    halfThirdScalingDoublePrefactor_pos
    halfThirdScalingDoublePrefactor_log_negligible



theorem generatedReplacedTCBRGPackage_bridge_doubled_by_package_comparison :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  generatedStableKeyReplacedTableClosedBallRGPackage
    |>.certificate_rgToExponentBridge_of_eventually_const_mul_le_le
      exampleScale
      (by
        apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
        exact halfThirdScalingCorrelationLength_exact_power)
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem generatedReplacedTCBRGPackage_valid_doubled_by_package_comparison :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  InfiniteTailTableClosedBallRGPackage.certificate_valid_of_eventually_const_mul_le_le
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    (by
      apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
      exact halfThirdScalingCorrelationLength_exact_power)
    halfThirdScalingCorrelationLength_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    halfThirdScalingDoubleComparison



theorem
    generatedReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_comparison :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β)
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent :=
  InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_const_mul_le_le
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    (by
      apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
      exact halfThirdScalingCorrelationLength_exact_power)
    halfThirdScalingCorrelationLength_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    halfThirdScalingDoubleComparison




theorem genStableReplacedTCB_bridge_doubled_by_comparison_congr_pred :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  generatedStableKeyReplacedTableClosedBallRGPackage
    |>.certificate_rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
      exampleScale
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      (by
        rw [generatedStableKeyReplacedTableClosedBallRGPackage_predictedExponent_eq]
        simpa [predictedNu, BlockScale.toReal, exampleScale,
          halfThirdScalingBlockScale] using
          halfThirdScalingRGCertificate_predictedExponent_eq.symm)
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem genStableReplacedTCB_valid_doubled_by_comparison_congr_pred :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  generatedStableKeyReplacedTableClosedBallRGPackage
    |>.certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent
      exampleScale
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      (by
        rw [generatedStableKeyReplacedTableClosedBallRGPackage_predictedExponent_eq]
        simpa [predictedNu, BlockScale.toReal, exampleScale,
          halfThirdScalingBlockScale] using
          halfThirdScalingRGCertificate_predictedExponent_eq.symm)
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem genStableReplacedTCB_hasCriticalNu_doubled_by_comparison_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β)
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent :=
  generatedStableKeyReplacedTableClosedBallRGPackage
    |>.certificate_hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent
      exampleScale
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      (by
        rw [generatedStableKeyReplacedTableClosedBallRGPackage_predictedExponent_eq]
        simpa [predictedNu, BlockScale.toReal, exampleScale,
          halfThirdScalingBlockScale] using
          halfThirdScalingRGCertificate_predictedExponent_eq.symm)
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem generatedReplacedTCBRGPackage_bridge_doubled_by_package_prefactor :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  generatedStableKeyReplacedTableClosedBallRGPackage
    |>.certificate_rgToExponentBridge_mul_log_negligible_prefactor
      exampleScale
      (by
        apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
        exact halfThirdScalingCorrelationLength_exact_power)
      halfThirdScalingCorrelationLength_pos
      halfThirdScalingDoublePrefactor_pos
      halfThirdScalingDoublePrefactor_log_negligible



theorem generatedReplacedTCBRGPackage_valid_doubled_by_package_prefactor :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  InfiniteTailTableClosedBallRGPackage.certificate_valid_mul_log_negligible_prefactor
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    (by
      apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
      exact halfThirdScalingCorrelationLength_exact_power)
    halfThirdScalingCorrelationLength_pos
    halfThirdScalingDoublePrefactor_pos
    halfThirdScalingDoublePrefactor_log_negligible



theorem generatedReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_prefactor :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β)
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent :=
  InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_mul_log_negligible_prefactor
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    (by
      apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
      exact halfThirdScalingCorrelationLength_exact_power)
    halfThirdScalingCorrelationLength_pos
    halfThirdScalingDoublePrefactor_pos
    halfThirdScalingDoublePrefactor_log_negligible



theorem genMinCubicKeyReplacedTCBRGPackage_bridge_doubled_by_package_comparison :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  genMinCubicKeyReplacedTableClosedBallRGPackage
    |>.certificate_rgToExponentBridge_of_eventually_const_mul_le_le
      exampleScale
      (by
        apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
        exact halfThirdScalingCorrelationLength_exact_power)
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem genMinCubicKeyReplacedTCBRGPackage_valid_doubled_by_package_comparison :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  InfiniteTailTableClosedBallRGPackage.certificate_valid_of_eventually_const_mul_le_le
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    (by
      apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
      exact halfThirdScalingCorrelationLength_exact_power)
    halfThirdScalingCorrelationLength_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    halfThirdScalingDoubleComparison



theorem
    genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_comparison :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β)
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent :=
  InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_const_mul_le_le
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    (by
      apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
      exact halfThirdScalingCorrelationLength_exact_power)
    halfThirdScalingCorrelationLength_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    halfThirdScalingDoubleComparison



theorem genMinCubicReplacedTCB_bridge_doubled_by_comparison_congr_pred :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  genMinCubicKeyReplacedTableClosedBallRGPackage
    |>.certificate_rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
      exampleScale
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      (by
        rw [genMinCubicKeyReplacedTableClosedBallRGPackage_predictedExponent_eq]
        simpa [predictedNu, BlockScale.toReal, exampleScale,
          halfThirdScalingBlockScale] using
          halfThirdScalingRGCertificate_predictedExponent_eq.symm)
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem genMinCubicReplacedTCB_valid_doubled_by_comparison_congr_pred :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  genMinCubicKeyReplacedTableClosedBallRGPackage
    |>.certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent
      exampleScale
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      (by
        rw [genMinCubicKeyReplacedTableClosedBallRGPackage_predictedExponent_eq]
        simpa [predictedNu, BlockScale.toReal, exampleScale,
          halfThirdScalingBlockScale] using
          halfThirdScalingRGCertificate_predictedExponent_eq.symm)
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem genMinCubicReplacedTCB_hasCriticalNu_doubled_by_comparison_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β)
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent :=
  genMinCubicKeyReplacedTableClosedBallRGPackage
    |>.certificate_hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent
      exampleScale
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      (by
        rw [genMinCubicKeyReplacedTableClosedBallRGPackage_predictedExponent_eq]
        simpa [predictedNu, BlockScale.toReal, exampleScale,
          halfThirdScalingBlockScale] using
          halfThirdScalingRGCertificate_predictedExponent_eq.symm)
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem genMinCubicKeyReplacedTCBRGPackage_bridge_doubled_by_package_prefactor :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  genMinCubicKeyReplacedTableClosedBallRGPackage
    |>.certificate_rgToExponentBridge_mul_log_negligible_prefactor
      exampleScale
      (by
        apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
        exact halfThirdScalingCorrelationLength_exact_power)
      halfThirdScalingCorrelationLength_pos
      halfThirdScalingDoublePrefactor_pos
      halfThirdScalingDoublePrefactor_log_negligible



theorem genMinCubicKeyReplacedTCBRGPackage_valid_doubled_by_package_prefactor :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  InfiniteTailTableClosedBallRGPackage.certificate_valid_mul_log_negligible_prefactor
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    (by
      apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
      exact halfThirdScalingCorrelationLength_exact_power)
    halfThirdScalingCorrelationLength_pos
    halfThirdScalingDoublePrefactor_pos
    halfThirdScalingDoublePrefactor_log_negligible



theorem genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_prefactor :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β)
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent :=
  InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_mul_log_negligible_prefactor
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    (by
      apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
      exact halfThirdScalingCorrelationLength_exact_power)
    halfThirdScalingCorrelationLength_pos
    halfThirdScalingDoublePrefactor_pos
    halfThirdScalingDoublePrefactor_log_negligible



theorem genBoundedCaseReplacedTCBRGPackage_bridge_doubled_by_package_comparison :
    (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  genBoundedCaseReplacedPackage
    |>.certificate_rgToExponentBridge_of_eventually_const_mul_le_le
      exampleScale
      (by
        apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
        exact halfThirdScalingCorrelationLength_exact_power)
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem genBoundedCaseReplacedTCBRGPackage_valid_doubled_by_package_comparison :
    (genBoundedCaseReplacedPackage.certificate exampleScale).Valid
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  InfiniteTailTableClosedBallRGPackage.certificate_valid_of_eventually_const_mul_le_le
    genBoundedCaseReplacedPackage
    exampleScale
    (by
      apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
      exact halfThirdScalingCorrelationLength_exact_power)
    halfThirdScalingCorrelationLength_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    halfThirdScalingDoubleComparison



theorem
    genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_comparison :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β)
      (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent :=
  InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_const_mul_le_le
    genBoundedCaseReplacedPackage
    exampleScale
    (by
      apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
      exact halfThirdScalingCorrelationLength_exact_power)
    halfThirdScalingCorrelationLength_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    halfThirdScalingDoubleComparison



theorem genBoundedCaseReplacedTCB_bridge_doubled_by_comparison_congr_pred :
    (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  genBoundedCaseReplacedPackage
    |>.certificate_rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
      exampleScale
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      (by
        rw [genBoundedCaseReplacedPackage_predictedExponent_eq]
        simpa [predictedNu, BlockScale.toReal, exampleScale,
          halfThirdScalingBlockScale] using
          halfThirdScalingRGCertificate_predictedExponent_eq.symm)
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem genBoundedCaseReplacedTCB_valid_doubled_by_comparison_congr_pred :
    (genBoundedCaseReplacedPackage.certificate exampleScale).Valid
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  genBoundedCaseReplacedPackage
    |>.certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent
      exampleScale
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      (by
        rw [genBoundedCaseReplacedPackage_predictedExponent_eq]
        simpa [predictedNu, BlockScale.toReal, exampleScale,
          halfThirdScalingBlockScale] using
          halfThirdScalingRGCertificate_predictedExponent_eq.symm)
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem genBoundedCaseReplacedTCB_hasCriticalNu_doubled_by_comparison_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β)
      (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent :=
  genBoundedCaseReplacedPackage
    |>.certificate_hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent
      exampleScale
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      (by
        rw [genBoundedCaseReplacedPackage_predictedExponent_eq]
        simpa [predictedNu, BlockScale.toReal, exampleScale,
          halfThirdScalingBlockScale] using
          halfThirdScalingRGCertificate_predictedExponent_eq.symm)
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem genBoundedCaseReplacedTCBRGPackage_bridge_doubled_by_package_prefactor :
    (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  genBoundedCaseReplacedPackage
    |>.certificate_rgToExponentBridge_mul_log_negligible_prefactor
      exampleScale
      (by
        apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
        exact halfThirdScalingCorrelationLength_exact_power)
      halfThirdScalingCorrelationLength_pos
      halfThirdScalingDoublePrefactor_pos
      halfThirdScalingDoublePrefactor_log_negligible



theorem genBoundedCaseReplacedTCBRGPackage_valid_doubled_by_package_prefactor :
    (genBoundedCaseReplacedPackage.certificate exampleScale).Valid
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  InfiniteTailTableClosedBallRGPackage.certificate_valid_mul_log_negligible_prefactor
    genBoundedCaseReplacedPackage
    exampleScale
    (by
      apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
      exact halfThirdScalingCorrelationLength_exact_power)
    halfThirdScalingCorrelationLength_pos
    halfThirdScalingDoublePrefactor_pos
    halfThirdScalingDoublePrefactor_log_negligible



theorem genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_prefactor :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β)
      (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent :=
  InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_mul_log_negligible_prefactor
    genBoundedCaseReplacedPackage
    exampleScale
    (by
      apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
      exact halfThirdScalingCorrelationLength_exact_power)
    halfThirdScalingCorrelationLength_pos
    halfThirdScalingDoublePrefactor_pos
    halfThirdScalingDoublePrefactor_log_negligible



theorem genCubicClassReplacedTCBRGPackage_bridge_doubled_by_package_comparison :
    (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  genCubicClassReplacedPackage
    |>.certificate_rgToExponentBridge_of_eventually_const_mul_le_le
      exampleScale
      (by
        apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
        exact halfThirdScalingCorrelationLength_exact_power)
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem genCubicClassReplacedTCBRGPackage_valid_doubled_by_package_comparison :
    (genCubicClassReplacedPackage.certificate exampleScale).Valid
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  InfiniteTailTableClosedBallRGPackage.certificate_valid_of_eventually_const_mul_le_le
    genCubicClassReplacedPackage
    exampleScale
    (by
      apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
      exact halfThirdScalingCorrelationLength_exact_power)
    halfThirdScalingCorrelationLength_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    halfThirdScalingDoubleComparison



theorem
    genCubicClassReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_comparison :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β)
      (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent :=
  InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_const_mul_le_le
    genCubicClassReplacedPackage
    exampleScale
    (by
      apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
      exact halfThirdScalingCorrelationLength_exact_power)
    halfThirdScalingCorrelationLength_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    halfThirdScalingDoubleComparison



theorem genCubicClassReplacedTCB_bridge_doubled_by_comparison_congr_pred :
    (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  genCubicClassReplacedPackage
    |>.certificate_rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent
      exampleScale
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      (by
        rw [genCubicClassReplacedPackage_predictedExponent_eq]
        simpa [predictedNu, BlockScale.toReal, exampleScale,
          halfThirdScalingBlockScale] using
          halfThirdScalingRGCertificate_predictedExponent_eq.symm)
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem genCubicClassReplacedTCB_valid_doubled_by_comparison_congr_pred :
    (genCubicClassReplacedPackage.certificate exampleScale).Valid
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  genCubicClassReplacedPackage
    |>.certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent
      exampleScale
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      (by
        rw [genCubicClassReplacedPackage_predictedExponent_eq]
        simpa [predictedNu, BlockScale.toReal, exampleScale,
          halfThirdScalingBlockScale] using
          halfThirdScalingRGCertificate_predictedExponent_eq.symm)
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem genCubicClassReplacedTCB_hasCriticalNu_doubled_by_comparison_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β)
      (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent :=
  genCubicClassReplacedPackage
    |>.certificate_hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent
      exampleScale
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      (by
        rw [genCubicClassReplacedPackage_predictedExponent_eq]
        simpa [predictedNu, BlockScale.toReal, exampleScale,
          halfThirdScalingBlockScale] using
          halfThirdScalingRGCertificate_predictedExponent_eq.symm)
      halfThirdScalingCorrelationLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubleComparison



theorem genCubicClassReplacedTCBRGPackage_bridge_doubled_by_package_prefactor :
    (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  genCubicClassReplacedPackage
    |>.certificate_rgToExponentBridge_mul_log_negligible_prefactor
      exampleScale
      (by
        apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
        exact halfThirdScalingCorrelationLength_exact_power)
      halfThirdScalingCorrelationLength_pos
      halfThirdScalingDoublePrefactor_pos
      halfThirdScalingDoublePrefactor_log_negligible



theorem genCubicClassReplacedTCBRGPackage_valid_doubled_by_package_prefactor :
    (genCubicClassReplacedPackage.certificate exampleScale).Valid
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β) :=
  InfiniteTailTableClosedBallRGPackage.certificate_valid_mul_log_negligible_prefactor
    genCubicClassReplacedPackage
    exampleScale
    (by
      apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
      exact halfThirdScalingCorrelationLength_exact_power)
    halfThirdScalingCorrelationLength_pos
    halfThirdScalingDoublePrefactor_pos
    halfThirdScalingDoublePrefactor_log_negligible



theorem genCubicClassReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_prefactor :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      (fun β =>
        halfThirdScalingDoublePrefactor β *
          halfThirdScalingCorrelationLength β)
      (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent :=
  InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_mul_log_negligible_prefactor
    genCubicClassReplacedPackage
    exampleScale
    (by
      apply RGCertificate.rgToExponentBridge_of_eventually_exact_power
      exact halfThirdScalingCorrelationLength_exact_power)
    halfThirdScalingCorrelationLength_pos
    halfThirdScalingDoublePrefactor_pos
    halfThirdScalingDoublePrefactor_log_negligible



noncomputable def geometricTailCorrelationLength (β : ℝ) : ℝ :=
  Real.exp
    (-geometricTailWitnessPackage.certificate.predictedExponent *
      Real.log ((ToyCriticalModel exampleScale 3).betaC - β))



theorem geometricTailCorrelationLength_eventually_pos :
    ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC
        (Set.Iio (ToyCriticalModel exampleScale 3).betaC),
      0 < geometricTailCorrelationLength β :=
  Filter.Eventually.of_forall fun _ => Real.exp_pos _



theorem geometricTailCorrelationLength_exact_power :
    ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC
        (Set.Iio (ToyCriticalModel exampleScale 3).betaC),
      geometricTailCorrelationLength β =
        Real.exp
          (-geometricTailWitnessPackage.certificate.predictedExponent *
            Real.log ((ToyCriticalModel exampleScale 3).betaC - β)) :=
  Filter.Eventually.of_forall fun _ => by
    rfl



theorem geometricTailWitnessBridge :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      geometricTailCorrelationLength :=
  RGCertificate.rgToExponentBridge_of_eventually_exact_power
    geometricTailWitnessPackage.certificate
    geometricTailCorrelationLength
    geometricTailCorrelationLength_exact_power


noncomputable def doubledGeometricTailCorrelationLength (β : ℝ) : ℝ :=
  2 * geometricTailCorrelationLength β



theorem doubledGeometricTailCorrelationLength_comparable :
    ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC
        (Set.Iio (ToyCriticalModel exampleScale 3).betaC),
      (2 : ℝ) * geometricTailCorrelationLength β ≤
          doubledGeometricTailCorrelationLength β ∧
        doubledGeometricTailCorrelationLength β ≤
          (2 : ℝ) * geometricTailCorrelationLength β :=
  Filter.Eventually.of_forall fun _ => by
    simp [doubledGeometricTailCorrelationLength]



theorem geometricTailWitness_bridge_doubled_by_package_comparison :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      doubledGeometricTailCorrelationLength :=
  geometricTailWitnessPackage.rgToExponentBridge_of_eventually_const_mul_le_le
    geometricTailWitnessBridge
    geometricTailCorrelationLength_eventually_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    doubledGeometricTailCorrelationLength_comparable



theorem geometricTailWitness_valid_doubled_by_package_comparison :
    geometricTailWitnessPackage.certificate.Valid
      doubledGeometricTailCorrelationLength :=
  geometricTailWitnessPackage.valid_of_eventually_const_mul_le_le
    geometricTailWitnessBridge
    geometricTailCorrelationLength_eventually_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    doubledGeometricTailCorrelationLength_comparable



theorem geometricTailWitness_hasCriticalNu_doubled_by_package_comparison :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      doubledGeometricTailCorrelationLength
      geometricTailWitnessPackage.certificate.predictedExponent :=
  geometricTailWitnessPackage.hasCriticalNu_of_eventually_const_mul_le_le
    geometricTailWitnessBridge
    geometricTailCorrelationLength_eventually_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    doubledGeometricTailCorrelationLength_comparable



noncomputable def contributionSplitInfiniteTailCorrelationLength
    (β : ℝ) : ℝ :=
  Real.exp
    (-contributionSplitAsInfiniteTailPackage.certificate.predictedExponent *
      Real.log ((ToyCriticalModel exampleScale 3).betaC - β))



theorem contributionSplitInfiniteTailCorrelationLength_eventually_pos :
    ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC
        (Set.Iio (ToyCriticalModel exampleScale 3).betaC),
      0 < contributionSplitInfiniteTailCorrelationLength β :=
  Filter.Eventually.of_forall fun _ => Real.exp_pos _



theorem contributionSplitInfiniteTailCorrelationLength_exact_power :
    ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC
        (Set.Iio (ToyCriticalModel exampleScale 3).betaC),
      contributionSplitInfiniteTailCorrelationLength β =
        Real.exp
          (-contributionSplitAsInfiniteTailPackage.certificate.predictedExponent *
            Real.log ((ToyCriticalModel exampleScale 3).betaC - β)) :=
  Filter.Eventually.of_forall fun _ => by
    rfl



theorem contributionSplitInfiniteTailPackageBridge :
    contributionSplitAsInfiniteTailPackage.certificate.RGToExponentBridge
      contributionSplitInfiniteTailCorrelationLength :=
  RGCertificate.rgToExponentBridge_of_eventually_exact_power
    contributionSplitAsInfiniteTailPackage.certificate
    contributionSplitInfiniteTailCorrelationLength
    contributionSplitInfiniteTailCorrelationLength_exact_power


noncomputable def doubledContributionSplitInfiniteTailCorrelationLength
    (β : ℝ) : ℝ :=
  2 * contributionSplitInfiniteTailCorrelationLength β



theorem doubledContributionSplitInfiniteTailCorrelationLength_comparable :
    ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC
        (Set.Iio (ToyCriticalModel exampleScale 3).betaC),
      (2 : ℝ) * contributionSplitInfiniteTailCorrelationLength β ≤
          doubledContributionSplitInfiniteTailCorrelationLength β ∧
        doubledContributionSplitInfiniteTailCorrelationLength β ≤
          (2 : ℝ) * contributionSplitInfiniteTailCorrelationLength β :=
  Filter.Eventually.of_forall fun _ => by
    simp [doubledContributionSplitInfiniteTailCorrelationLength]



theorem contributionSplitInfiniteTail_bridge_doubled_by_package_comparison :
    contributionSplitAsInfiniteTailPackage.certificate.RGToExponentBridge
      doubledContributionSplitInfiniteTailCorrelationLength :=
  contributionSplitAsInfiniteTailPackage
    |>.rgToExponentBridge_of_eventually_const_mul_le_le
      contributionSplitInfiniteTailPackageBridge
      contributionSplitInfiniteTailCorrelationLength_eventually_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      doubledContributionSplitInfiniteTailCorrelationLength_comparable



theorem
    contributionSplitInfiniteTail_valid_doubled_by_package_comparison :
    contributionSplitAsInfiniteTailPackage.certificate.Valid
      doubledContributionSplitInfiniteTailCorrelationLength :=
  contributionSplitAsInfiniteTailPackage.valid_of_eventually_const_mul_le_le
    contributionSplitInfiniteTailPackageBridge
    contributionSplitInfiniteTailCorrelationLength_eventually_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    doubledContributionSplitInfiniteTailCorrelationLength_comparable



theorem
    contributionSplitInfiniteTail_hasCriticalNu_doubled_by_package_comparison :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      doubledContributionSplitInfiniteTailCorrelationLength
      contributionSplitAsInfiniteTailPackage.certificate.predictedExponent :=
  contributionSplitAsInfiniteTailPackage.hasCriticalNu_of_eventually_const_mul_le_le
    contributionSplitInfiniteTailPackageBridge
    contributionSplitInfiniteTailCorrelationLength_eventually_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    doubledContributionSplitInfiniteTailCorrelationLength_comparable



noncomputable abbrev zeroStableKeyTableWitnessPackage :=
  zeroTableClosedBallRGPackage.tableWitness



noncomputable def zeroStableKeyTableWitnessCorrelationLength
    (β : ℝ) : ℝ :=
  Real.exp
    (-zeroStableKeyTableWitnessPackage.certificate.predictedExponent *
      Real.log ((ToyCriticalModel exampleScale 3).betaC - β))



theorem zeroStableKeyTableWitnessCorrelationLength_eventually_pos :
    ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC
        (Set.Iio (ToyCriticalModel exampleScale 3).betaC),
      0 < zeroStableKeyTableWitnessCorrelationLength β :=
  Filter.Eventually.of_forall fun _ => Real.exp_pos _



theorem zeroStableKeyTableWitnessCorrelationLength_exact_power :
    ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC
        (Set.Iio (ToyCriticalModel exampleScale 3).betaC),
      zeroStableKeyTableWitnessCorrelationLength β =
        Real.exp
          (-zeroStableKeyTableWitnessPackage.certificate.predictedExponent *
            Real.log ((ToyCriticalModel exampleScale 3).betaC - β)) :=
  Filter.Eventually.of_forall fun _ => by
    rfl



theorem zeroStableKeyTableWitnessBridge :
    zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge
      zeroStableKeyTableWitnessCorrelationLength :=
  RGCertificate.rgToExponentBridge_of_eventually_exact_power
    zeroStableKeyTableWitnessPackage.certificate
    zeroStableKeyTableWitnessCorrelationLength
    zeroStableKeyTableWitnessCorrelationLength_exact_power


noncomputable def doubledZeroStableKeyTableWitnessCorrelationLength
    (β : ℝ) : ℝ :=
  2 * zeroStableKeyTableWitnessCorrelationLength β



theorem doubledZeroStableKeyTableWitnessCorrelationLength_comparable :
    ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC
        (Set.Iio (ToyCriticalModel exampleScale 3).betaC),
      (2 : ℝ) * zeroStableKeyTableWitnessCorrelationLength β ≤
          doubledZeroStableKeyTableWitnessCorrelationLength β ∧
        doubledZeroStableKeyTableWitnessCorrelationLength β ≤
          (2 : ℝ) * zeroStableKeyTableWitnessCorrelationLength β :=
  Filter.Eventually.of_forall fun _ => by
    simp [doubledZeroStableKeyTableWitnessCorrelationLength]



theorem zeroStableKeyTableWitness_bridge_doubled_by_package_comparison :
    zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge
      doubledZeroStableKeyTableWitnessCorrelationLength :=
  zeroStableKeyTableWitnessPackage.rgToExponentBridge_of_eventually_const_mul_le_le
    zeroStableKeyTableWitnessBridge
    zeroStableKeyTableWitnessCorrelationLength_eventually_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    doubledZeroStableKeyTableWitnessCorrelationLength_comparable



theorem zeroStableKeyTableWitness_valid_doubled_by_package_comparison :
    zeroStableKeyTableWitnessPackage.certificate.Valid
      doubledZeroStableKeyTableWitnessCorrelationLength :=
  zeroStableKeyTableWitnessPackage.valid_of_eventually_const_mul_le_le
    zeroStableKeyTableWitnessBridge
    zeroStableKeyTableWitnessCorrelationLength_eventually_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    doubledZeroStableKeyTableWitnessCorrelationLength_comparable



theorem
    zeroStableKeyTableWitness_hasCriticalNu_doubled_by_package_comparison :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      doubledZeroStableKeyTableWitnessCorrelationLength
      zeroStableKeyTableWitnessPackage.certificate.predictedExponent :=
  zeroStableKeyTableWitnessPackage.hasCriticalNu_of_eventually_const_mul_le_le
    zeroStableKeyTableWitnessBridge
    zeroStableKeyTableWitnessCorrelationLength_eventually_pos
    (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2)
    doubledZeroStableKeyTableWitnessCorrelationLength_comparable

end PackageComparisonBridgeExample
end Exact3D
end StatMech

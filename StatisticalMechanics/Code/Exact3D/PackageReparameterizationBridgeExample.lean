/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.WitnessReparameterizationBridge
import Code.Exact3D.FinitePlusTailReparameterizationBridge
import Code.Exact3D.TableClosedBallReparameterizationBridge
import Code.Exact3D.FiniteWitnessPackageExample
import Code.Exact3D.FinitePlusTailContractionExample
import Code.Exact3D.PackageComparisonBridgeExample










namespace StatMech
namespace Exact3D
namespace PackageReparameterizationBridgeExample

open FiniteWitnessPackageExample
open FinitePlusTailContractionExample
open InfiniteTailWitnessPackageExample
open PackageComparisonBridgeExample
open FiniteWitnessPackage
open FinitePlusTailHyperbolicSplitting


noncomputable def hierarchicalLinearReparam (β : ℝ) : ℝ :=
  LeftCriticalReparam.linearMap HierarchicalModel HierarchicalModel 2 β


noncomputable def hierarchicalReparameterizedLength (β : ℝ) : ℝ :=
  hierarchicalCorrelationLength (hierarchicalLinearReparam β)



theorem hierarchicalLinearReparam_leftCritical :
    LeftCriticalReparam HierarchicalModel HierarchicalModel
      hierarchicalLinearReparam :=
  LeftCriticalReparam.linear HierarchicalModel HierarchicalModel
    (by norm_num : (0 : ℝ) < 2)



theorem hierarchicalReparameterizedLength_eventually_eq :
    ∀ᶠ β in nhdsWithin HierarchicalModel.betaC (Set.Iio HierarchicalModel.betaC),
      hierarchicalReparameterizedLength β =
        hierarchicalCorrelationLength (hierarchicalLinearReparam β) :=
  Filter.Eventually.of_forall fun _ => rfl



theorem hierarchicalWitness_hasCriticalNu_target :
    HasCriticalNu HierarchicalModel hierarchicalCorrelationLength
      hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent := by
  simpa [hierarchicalContributionSplitWitnessPackage_predictedExponent_eq,
    hierarchicalNu, hierarchicalCertificate, predictedNu] using
    hierarchical_hasCriticalNu



theorem hierarchicalWitness_predictedExponent_eq_hierarchicalNu :
    hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent =
      hierarchicalNu := by
  rw [hierarchicalContributionSplitWitnessPackage_predictedExponent_eq]
  rfl



theorem
    hierarchicalWitness_bridge_reparameterized_from_namedTargetExponent_congr :
    hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge
      hierarchicalReparameterizedLength :=
  hierarchicalContributionSplitWitnessPackage
    |>.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      hierarchicalWitness_predictedExponent_eq_hierarchicalNu
      hierarchical_hasCriticalNu
      hierarchicalLinearReparam_leftCritical
      hierarchicalReparameterizedLength_eventually_eq




theorem
    hierarchicalWitness_valid_reparameterized_from_namedTargetExponent_congr :
    hierarchicalContributionSplitWitnessPackage.certificate.Valid
      hierarchicalReparameterizedLength :=
  hierarchicalContributionSplitWitnessPackage
    |>.valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      hierarchicalWitness_predictedExponent_eq_hierarchicalNu
      hierarchical_hasCriticalNu
      hierarchicalLinearReparam_leftCritical
      hierarchicalReparameterizedLength_eventually_eq



theorem
    hierarchicalWitness_hasCriticalNu_reparameterized_from_namedTargetExponent_congr :
    HasCriticalNu HierarchicalModel hierarchicalReparameterizedLength
      hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent :=
  hierarchicalContributionSplitWitnessPackage
    |>.hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      hierarchicalWitness_predictedExponent_eq_hierarchicalNu
      hierarchical_hasCriticalNu
      hierarchicalLinearReparam_leftCritical
      hierarchicalReparameterizedLength_eventually_eq



theorem hierarchicalWitness_bridge_reparameterized_from_targetExponent :
    hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge
      hierarchicalReparameterizedLength :=
  hierarchicalContributionSplitWitnessPackage
    |>.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
      hierarchicalWitness_hasCriticalNu_target
      hierarchicalLinearReparam_leftCritical
      hierarchicalReparameterizedLength_eventually_eq



theorem hierarchicalWitness_valid_reparameterized_from_targetExponent :
    hierarchicalContributionSplitWitnessPackage.certificate.Valid
      hierarchicalReparameterizedLength :=
  hierarchicalContributionSplitWitnessPackage.valid_of_reparameterized_hasCriticalNu_eventually_eq
    hierarchicalWitness_hasCriticalNu_target
    hierarchicalLinearReparam_leftCritical
    hierarchicalReparameterizedLength_eventually_eq



theorem hierarchicalWitness_hasCriticalNu_reparameterized_from_targetExponent :
    HasCriticalNu HierarchicalModel hierarchicalReparameterizedLength
      hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent :=
  hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    hierarchicalContributionSplitWitnessPackage
    hierarchicalWitness_hasCriticalNu_target
    hierarchicalLinearReparam_leftCritical
    hierarchicalReparameterizedLength_eventually_eq



theorem hierarchicalCertificate_predicted_eq_witness :
    hierarchicalCertificate.predictedExponent =
      hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent := by
  rw [hierarchicalContributionSplitWitnessPackage_predictedExponent_eq]
  rfl



theorem hierarchicalWitness_bridge_reparameterized_from_externalBridge :
    hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge
      hierarchicalReparameterizedLength :=
  hierarchicalContributionSplitWitnessPackage
    |>.rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
      hierarchicalCertificate
      hierarchicalCertificate_predicted_eq_witness
      hierarchical_bridge_via_exact_power
      hierarchicalLinearReparam_leftCritical
      hierarchicalReparameterizedLength_eventually_eq



theorem hierarchicalWitness_valid_reparameterized_from_externalBridge :
    hierarchicalContributionSplitWitnessPackage.certificate.Valid
      hierarchicalReparameterizedLength :=
  valid_of_reparameterized_rgToExponentBridge_eventually_eq
    hierarchicalContributionSplitWitnessPackage
    hierarchicalCertificate
    hierarchicalCertificate_predicted_eq_witness
    hierarchical_bridge_via_exact_power
    hierarchicalLinearReparam_leftCritical
    hierarchicalReparameterizedLength_eventually_eq



theorem hierarchicalWitness_hasCriticalNu_reparameterized_from_externalBridge :
    HasCriticalNu HierarchicalModel hierarchicalReparameterizedLength
      hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent :=
  hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    hierarchicalContributionSplitWitnessPackage
    hierarchicalCertificate
    hierarchicalCertificate_predicted_eq_witness
    hierarchical_bridge_via_exact_power
    hierarchicalLinearReparam_leftCritical
    hierarchicalReparameterizedLength_eventually_eq



theorem hierarchicalWitnessRetargetBridge :
    (hierarchicalContributionSplitWitnessPackage.certificate.retarget
      HierarchicalModel).RGToExponentBridge hierarchicalCorrelationLength := by
  change HasCriticalNu HierarchicalModel hierarchicalCorrelationLength
    (hierarchicalContributionSplitWitnessPackage.certificate.retarget
      HierarchicalModel).predictedExponent
  simpa using hierarchicalWitness_hasCriticalNu_target



theorem hierarchicalWitness_bridge_reparameterized_from_retargetBridge :
    hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge
      hierarchicalReparameterizedLength :=
  hierarchicalContributionSplitWitnessPackage
    |>.rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
      hierarchicalWitnessRetargetBridge
      hierarchicalLinearReparam_leftCritical
      hierarchicalReparameterizedLength_eventually_eq



theorem hierarchicalWitness_valid_reparameterized_from_retargetBridge :
    hierarchicalContributionSplitWitnessPackage.certificate.Valid
      hierarchicalReparameterizedLength :=
  hierarchicalContributionSplitWitnessPackage.valid_of_reparameterized_retargetBridge_eventually_eq
    hierarchicalWitnessRetargetBridge
    hierarchicalLinearReparam_leftCritical
    hierarchicalReparameterizedLength_eventually_eq



theorem hierarchicalWitness_hasCriticalNu_reparameterized_from_retargetBridge :
    HasCriticalNu HierarchicalModel hierarchicalReparameterizedLength
      hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent :=
  FiniteWitnessPackage.hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    hierarchicalContributionSplitWitnessPackage
    hierarchicalWitnessRetargetBridge
    hierarchicalLinearReparam_leftCritical
    hierarchicalReparameterizedLength_eventually_eq



noncomputable def halfThirdScalingLinearReparam (β : ℝ) : ℝ :=
  LeftCriticalReparam.linearMap
    halfThirdScalingModel halfThirdScalingModel 2 β



noncomputable def halfThirdScalingReparameterizedLength (β : ℝ) : ℝ :=
  halfThirdScalingCorrelationLength (halfThirdScalingLinearReparam β)



theorem halfThirdScalingLinearReparam_leftCritical :
    LeftCriticalReparam halfThirdScalingModel halfThirdScalingModel
      halfThirdScalingLinearReparam :=
  LeftCriticalReparam.linear halfThirdScalingModel halfThirdScalingModel
    (by norm_num : (0 : ℝ) < 2)



theorem halfThirdScalingReparameterizedLength_eventually_eq :
    ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC),
      halfThirdScalingReparameterizedLength β =
        halfThirdScalingCorrelationLength
          (halfThirdScalingLinearReparam β) :=
  Filter.Eventually.of_forall fun _ => rfl



theorem halfThirdScalingHyperbolicSplitting_bridge_reparameterized :
    halfThirdScalingRGCertificate.RGToExponentBridge
      halfThirdScalingReparameterizedLength := by
  simpa [halfThirdScalingRGCertificate] using
    certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
      halfThirdScalingHyperbolicSplitting
      halfThirdScalingBlockScale
      halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs
      halfThirdScalingLinearReparam_leftCritical
      halfThirdScalingReparameterizedLength_eventually_eq




theorem halfThirdScalingHyperbolicSplitting_valid_reparameterized :
    halfThirdScalingRGCertificate.Valid
      halfThirdScalingReparameterizedLength := by
  simpa [halfThirdScalingRGCertificate] using
    certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
      halfThirdScalingHyperbolicSplitting
      halfThirdScalingBlockScale
      halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs
      halfThirdScalingLinearReparam_leftCritical
      halfThirdScalingReparameterizedLength_eventually_eq



theorem halfThirdScalingHyperbolicSplitting_hasCriticalNu_reparameterized :
    HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength
      halfThirdScalingRGCertificate.predictedExponent := by
  simpa [halfThirdScalingRGCertificate] using
    certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
      halfThirdScalingHyperbolicSplitting
      halfThirdScalingBlockScale
      halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs
      halfThirdScalingLinearReparam_leftCritical
      halfThirdScalingReparameterizedLength_eventually_eq



theorem
    halfThirdScalingHyperbolicSplitting_bridge_reparameterized_from_externalBridge :
    halfThirdScalingRGCertificate.RGToExponentBridge
      halfThirdScalingReparameterizedLength := by
  simpa [halfThirdScalingRGCertificate] using
    certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
      halfThirdScalingHyperbolicSplitting
      halfThirdScalingBlockScale
      halfThirdScalingRGCertificate
      rfl
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      halfThirdScalingLinearReparam_leftCritical
      halfThirdScalingReparameterizedLength_eventually_eq



theorem halfThirdScalingHyperbolicSplitting_valid_reparameterized_from_externalBridge :
    halfThirdScalingRGCertificate.Valid
      halfThirdScalingReparameterizedLength := by
  simpa [halfThirdScalingRGCertificate] using
    certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq
      halfThirdScalingHyperbolicSplitting
      halfThirdScalingBlockScale
      halfThirdScalingRGCertificate
      rfl
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      halfThirdScalingLinearReparam_leftCritical
      halfThirdScalingReparameterizedLength_eventually_eq



theorem
    halfThirdScalingHyperbolicSplitting_hasCriticalNu_reparameterized_from_externalBridge :
    HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength
      halfThirdScalingRGCertificate.predictedExponent := by
  simpa [halfThirdScalingRGCertificate] using
    certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
      halfThirdScalingHyperbolicSplitting
      halfThirdScalingBlockScale
      halfThirdScalingRGCertificate
      rfl
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      halfThirdScalingLinearReparam_leftCritical
      halfThirdScalingReparameterizedLength_eventually_eq



theorem halfThirdScalingHyperbolicSplittingRetargetBridge :
    ((halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).retarget
        halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength := by
  change HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength
    ((halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).retarget
        halfThirdScalingModel).predictedExponent
  simpa [halfThirdScalingRGCertificate] using
    halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs



theorem
    halfThirdScalingHyperbolicSplitting_bridge_reparameterized_from_retargetBridge :
    halfThirdScalingRGCertificate.RGToExponentBridge
      halfThirdScalingReparameterizedLength := by
  simpa [halfThirdScalingRGCertificate] using
    certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
      halfThirdScalingHyperbolicSplitting
      halfThirdScalingBlockScale
      halfThirdScalingHyperbolicSplittingRetargetBridge
      halfThirdScalingLinearReparam_leftCritical
      halfThirdScalingReparameterizedLength_eventually_eq




theorem halfThirdScalingHyperbolicSplitting_valid_reparameterized_from_retargetBridge :
    halfThirdScalingRGCertificate.Valid
      halfThirdScalingReparameterizedLength := by
  simpa [halfThirdScalingRGCertificate] using
    certificate_valid_of_reparameterized_retargetBridge_eventually_eq
      halfThirdScalingHyperbolicSplitting
      halfThirdScalingBlockScale
      halfThirdScalingHyperbolicSplittingRetargetBridge
      halfThirdScalingLinearReparam_leftCritical
      halfThirdScalingReparameterizedLength_eventually_eq




theorem
    halfThirdScalingHyperbolicSplitting_hasCriticalNu_reparameterized_from_retargetBridge :
    HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength
      halfThirdScalingRGCertificate.predictedExponent := by
  simpa [halfThirdScalingRGCertificate] using
    certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
      halfThirdScalingHyperbolicSplitting
      halfThirdScalingBlockScale
      halfThirdScalingHyperbolicSplittingRetargetBridge
      halfThirdScalingLinearReparam_leftCritical
      halfThirdScalingReparameterizedLength_eventually_eq




theorem halfThirdScalingBlockRGPackage_bridge_reparameterized_from_congrTarget :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingBlockRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent
    halfThirdScalingBlockScale
    (by
      rw [halfThirdScalingBlockRGPackage_predictedExponent_eq,
        halfThirdScalingRGCertificate_predictedExponent_eq])
    halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq



theorem halfThirdScalingBlockRGPackage_valid_reparameterized_from_congrTarget :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingBlockRGPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    halfThirdScalingBlockScale
    (by
      rw [halfThirdScalingBlockRGPackage_predictedExponent_eq,
        halfThirdScalingRGCertificate_predictedExponent_eq])
    halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq



theorem halfThirdScalingBlockRGPackage_hasCriticalNu_reparameterized_from_congrTarget :
    HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength
      (halfThirdScalingBlockRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  let P := halfThirdScalingBlockRGPackage
  exact
    (P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      halfThirdScalingBlockScale
      (by
        rw [halfThirdScalingBlockRGPackage_predictedExponent_eq,
          halfThirdScalingRGCertificate_predictedExponent_eq])
      halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs
      halfThirdScalingLinearReparam_leftCritical
      halfThirdScalingReparameterizedLength_eventually_eq).hasCriticalNu




theorem halfThirdScalingBlockRGPackage_bridge_reparameterized :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingBlockRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingBlockRGCertificate_hasCriticalNu_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq




theorem halfThirdScalingBlockRGPackage_valid_reparameterized :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingBlockRGPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingBlockRGCertificate_hasCriticalNu_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq



theorem halfThirdScalingBlockRGPackage_hasCriticalNu_reparameterized :
    HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength
      (halfThirdScalingBlockRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  let P := halfThirdScalingBlockRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingBlockRGCertificate_hasCriticalNu_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq




theorem
    halfThirdScalingBlockRGPackage_bridge_reparameterized_from_externalBridge :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingBlockRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingBlockRGCertificate
    rfl
    halfThirdScalingBlockRGCertificate_bridge_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq




theorem halfThirdScalingBlockRGPackage_valid_reparameterized_from_externalBridge :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingBlockRGPackage
  exact P.certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingBlockRGCertificate
    rfl
    halfThirdScalingBlockRGCertificate_bridge_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq



theorem halfThirdScalingBlockRGPackage_hasCriticalNu_reparameterized_from_externalBridge :
    HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength
      (halfThirdScalingBlockRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  let P := halfThirdScalingBlockRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingBlockRGCertificate
    rfl
    halfThirdScalingBlockRGCertificate_bridge_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq



theorem halfThirdScalingBlockRGPackageRetargetBridge :
    ((halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).retarget
        halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength := by
  change HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength
    ((halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).retarget
        halfThirdScalingModel).predictedExponent
  simpa [halfThirdScalingBlockRGCertificate] using
    halfThirdScalingBlockRGCertificate_hasCriticalNu_from_prefactorInputs



theorem halfThirdScalingBlockRGPackage_bridge_reparameterized_from_retargetBridge :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingBlockRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingBlockRGPackageRetargetBridge
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq




theorem halfThirdScalingBlockRGPackage_valid_reparameterized_from_retargetBridge :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingBlockRGPackage
  exact P.certificate_valid_of_reparameterized_retargetBridge_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingBlockRGPackageRetargetBridge
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq



theorem halfThirdScalingBlockRGPackage_hasCriticalNu_reparameterized_from_retargetBridge :
    HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength
      (halfThirdScalingBlockRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  let P := halfThirdScalingBlockRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingBlockRGPackageRetargetBridge
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq




theorem halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_target :
    HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  simpa [halfThirdScalingUnitClosedBallRGPackage_predictedExponent_eq,
    halfThirdScalingRGCertificate_predictedExponent_eq] using
    halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs



theorem
    halfThirdScalingUnitClosedBallRGPackage_bridge_reparameterized_from_congrTarget :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingUnitClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent
    halfThirdScalingBlockScale
    (by
      rw [halfThirdScalingUnitClosedBallRGPackage_predictedExponent_eq,
        halfThirdScalingRGCertificate_predictedExponent_eq])
    halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq



theorem
    halfThirdScalingUnitClosedBallRGPackage_valid_reparameterized_from_congrTarget :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingUnitClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    halfThirdScalingBlockScale
    (by
      rw [halfThirdScalingUnitClosedBallRGPackage_predictedExponent_eq,
        halfThirdScalingRGCertificate_predictedExponent_eq])
    halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq



theorem
    halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_reparameterized_from_congrTarget :
    HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  let P := halfThirdScalingUnitClosedBallRGPackage
  exact
    (P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      halfThirdScalingBlockScale
      (by
        rw [halfThirdScalingUnitClosedBallRGPackage_predictedExponent_eq,
          halfThirdScalingRGCertificate_predictedExponent_eq])
      halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs
      halfThirdScalingLinearReparam_leftCritical
      halfThirdScalingReparameterizedLength_eventually_eq).hasCriticalNu



theorem halfThirdScalingUnitClosedBallRGPackage_bridge_reparameterized :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingUnitClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_target
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq




theorem halfThirdScalingUnitClosedBallRGPackage_valid_reparameterized :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingUnitClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_target
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq



theorem halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_reparameterized :
    HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  let P := halfThirdScalingUnitClosedBallRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_target
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq




theorem
    halfThirdScalingUnitClosedBallRGPackage_bridge_reparameterized_from_externalBridge :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingUnitClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingRGCertificate
    (by
      rw [halfThirdScalingRGCertificate_predictedExponent_eq,
        halfThirdScalingUnitClosedBallRGPackage_predictedExponent_eq])
    halfThirdScalingRGCertificate_bridge_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq




theorem
    halfThirdScalingUnitClosedBallRGPackage_valid_reparameterized_from_externalBridge :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingUnitClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingRGCertificate
    (by
      rw [halfThirdScalingRGCertificate_predictedExponent_eq,
        halfThirdScalingUnitClosedBallRGPackage_predictedExponent_eq])
    halfThirdScalingRGCertificate_bridge_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq



theorem
    halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_reparameterized_from_externalBridge :
    HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  let P := halfThirdScalingUnitClosedBallRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingRGCertificate
    (by
      rw [halfThirdScalingRGCertificate_predictedExponent_eq,
        halfThirdScalingUnitClosedBallRGPackage_predictedExponent_eq])
    halfThirdScalingRGCertificate_bridge_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq



theorem halfThirdScalingUnitClosedBallRGPackageRetargetBridge :
    ((halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).retarget
        halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength := by
  change HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength
    ((halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).retarget
        halfThirdScalingModel).predictedExponent
  simpa using halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_target




theorem
    halfThirdScalingUnitClosedBallRGPackage_bridge_reparameterized_from_retargetBridge :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingUnitClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingUnitClosedBallRGPackageRetargetBridge
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq




theorem
    halfThirdScalingUnitClosedBallRGPackage_valid_reparameterized_from_retargetBridge :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingUnitClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_retargetBridge_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingUnitClosedBallRGPackageRetargetBridge
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq



theorem
    halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_reparameterized_from_retargetBridge :
    HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  let P := halfThirdScalingUnitClosedBallRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingUnitClosedBallRGPackageRetargetBridge
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq



noncomputable def toyLinearReparam (β : ℝ) : ℝ :=
  LeftCriticalReparam.linearMap
    (ToyCriticalModel exampleScale 3) (ToyCriticalModel exampleScale 3) 2 β



theorem toyLinearReparam_leftCritical :
    LeftCriticalReparam (ToyCriticalModel exampleScale 3)
      (ToyCriticalModel exampleScale 3) toyLinearReparam :=
  LeftCriticalReparam.linear
    (ToyCriticalModel exampleScale 3) (ToyCriticalModel exampleScale 3)
    (by norm_num : (0 : ℝ) < 2)



noncomputable def geometricTailReparameterizedCorrelationLength
    (β : ℝ) : ℝ :=
  geometricTailCorrelationLength (toyLinearReparam β)



theorem geometricTailReparameterizedCorrelationLength_eventually_eq :
    ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC
        (Set.Iio (ToyCriticalModel exampleScale 3).betaC),
      geometricTailReparameterizedCorrelationLength β =
        geometricTailCorrelationLength (toyLinearReparam β) :=
  Filter.Eventually.of_forall fun _ => rfl



theorem geometricTailWitness_hasCriticalNu_target :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      geometricTailCorrelationLength
      geometricTailWitnessPackage.certificate.predictedExponent :=
  geometricTailWitnessPackage.hasCriticalNu_of_bridge
    geometricTailWitnessBridge



theorem geometricTailWitness_predictedExponent_eq :
    geometricTailWitnessPackage.certificate.predictedExponent =
      predictedNu exampleScale 3 := by
  rw [InfiniteTailWitnessPackage.certificate_predictedExponent_eq]
  rfl



theorem geometricTailWitness_hasCriticalNu_formulaTarget :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      geometricTailCorrelationLength (predictedNu exampleScale 3) := by
  simpa [geometricTailWitness_predictedExponent_eq] using
    geometricTailWitness_hasCriticalNu_target




theorem geometricTailWitness_bridge_reparameterized_from_congrTarget :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      geometricTailReparameterizedCorrelationLength :=
  geometricTailWitnessPackage
    |>.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      geometricTailWitness_predictedExponent_eq
      geometricTailWitness_hasCriticalNu_formulaTarget
      toyLinearReparam_leftCritical
      geometricTailReparameterizedCorrelationLength_eventually_eq


theorem geometricTailWitness_valid_reparameterized_from_congrTarget :
    geometricTailWitnessPackage.certificate.Valid
      geometricTailReparameterizedCorrelationLength :=
  geometricTailWitnessPackage
    |>.valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      geometricTailWitness_predictedExponent_eq
      geometricTailWitness_hasCriticalNu_formulaTarget
      toyLinearReparam_leftCritical
      geometricTailReparameterizedCorrelationLength_eventually_eq



theorem geometricTailWitness_hasCriticalNu_reparameterized_from_congrTarget :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      geometricTailReparameterizedCorrelationLength
      geometricTailWitnessPackage.certificate.predictedExponent :=
  (geometricTailWitnessPackage
    |>.valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      geometricTailWitness_predictedExponent_eq
      geometricTailWitness_hasCriticalNu_formulaTarget
      toyLinearReparam_leftCritical
      geometricTailReparameterizedCorrelationLength_eventually_eq).hasCriticalNu



theorem geometricTailWitness_bridge_reparameterized_from_targetExponent :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      geometricTailReparameterizedCorrelationLength :=
  geometricTailWitnessPackage
    |>.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
      geometricTailWitness_hasCriticalNu_target
      toyLinearReparam_leftCritical
      geometricTailReparameterizedCorrelationLength_eventually_eq



theorem geometricTailWitness_valid_reparameterized_from_targetExponent :
    geometricTailWitnessPackage.certificate.Valid
      geometricTailReparameterizedCorrelationLength :=
  geometricTailWitnessPackage.valid_of_reparameterized_hasCriticalNu_eventually_eq
    geometricTailWitness_hasCriticalNu_target
    toyLinearReparam_leftCritical
    geometricTailReparameterizedCorrelationLength_eventually_eq



theorem geometricTailWitness_hasCriticalNu_reparameterized_from_targetExponent :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      geometricTailReparameterizedCorrelationLength
      geometricTailWitnessPackage.certificate.predictedExponent :=
  geometricTailWitnessPackage.hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    geometricTailWitness_hasCriticalNu_target
    toyLinearReparam_leftCritical
    geometricTailReparameterizedCorrelationLength_eventually_eq



theorem geometricTailWitness_bridge_reparameterized_from_externalBridge :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      geometricTailReparameterizedCorrelationLength :=
  geometricTailWitnessPackage
    |>.rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
      geometricTailWitnessPackage.certificate
      rfl
      geometricTailWitnessBridge
      toyLinearReparam_leftCritical
      geometricTailReparameterizedCorrelationLength_eventually_eq



theorem geometricTailWitness_valid_reparameterized_from_externalBridge :
    geometricTailWitnessPackage.certificate.Valid
      geometricTailReparameterizedCorrelationLength :=
  geometricTailWitnessPackage.valid_of_reparameterized_rgToExponentBridge_eventually_eq
    geometricTailWitnessPackage.certificate
    rfl
    geometricTailWitnessBridge
    toyLinearReparam_leftCritical
    geometricTailReparameterizedCorrelationLength_eventually_eq



theorem geometricTailWitness_hasCriticalNu_reparameterized_from_externalBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      geometricTailReparameterizedCorrelationLength
      geometricTailWitnessPackage.certificate.predictedExponent :=
  geometricTailWitnessPackage.hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    geometricTailWitnessPackage.certificate
    rfl
    geometricTailWitnessBridge
    toyLinearReparam_leftCritical
    geometricTailReparameterizedCorrelationLength_eventually_eq



theorem geometricTailWitnessRetargetBridge :
    (geometricTailWitnessPackage.certificate.retarget
      (ToyCriticalModel exampleScale 3)).RGToExponentBridge
        geometricTailCorrelationLength := by
  change HasCriticalNu (ToyCriticalModel exampleScale 3)
    geometricTailCorrelationLength
    (geometricTailWitnessPackage.certificate.retarget
      (ToyCriticalModel exampleScale 3)).predictedExponent
  simpa using geometricTailWitness_hasCriticalNu_target



theorem geometricTailWitness_bridge_reparameterized_from_retargetBridge :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      geometricTailReparameterizedCorrelationLength :=
  geometricTailWitnessPackage
    |>.rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
      geometricTailWitnessRetargetBridge
      toyLinearReparam_leftCritical
      geometricTailReparameterizedCorrelationLength_eventually_eq



theorem geometricTailWitness_valid_reparameterized_from_retargetBridge :
    geometricTailWitnessPackage.certificate.Valid
      geometricTailReparameterizedCorrelationLength :=
  geometricTailWitnessPackage.valid_of_reparameterized_retargetBridge_eventually_eq
    geometricTailWitnessRetargetBridge
    toyLinearReparam_leftCritical
    geometricTailReparameterizedCorrelationLength_eventually_eq



theorem geometricTailWitness_hasCriticalNu_reparameterized_from_retargetBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      geometricTailReparameterizedCorrelationLength
      geometricTailWitnessPackage.certificate.predictedExponent :=
  geometricTailWitnessPackage.hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    geometricTailWitnessRetargetBridge
    toyLinearReparam_leftCritical
    geometricTailReparameterizedCorrelationLength_eventually_eq



noncomputable def zeroStableKeyTableWitnessReparameterizedCorrelationLength
    (β : ℝ) : ℝ :=
  zeroStableKeyTableWitnessCorrelationLength (toyLinearReparam β)



theorem
    zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq :
    ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC
        (Set.Iio (ToyCriticalModel exampleScale 3).betaC),
      zeroStableKeyTableWitnessReparameterizedCorrelationLength β =
        zeroStableKeyTableWitnessCorrelationLength (toyLinearReparam β) :=
  Filter.Eventually.of_forall fun _ => rfl



theorem zeroStableKeyTableWitness_hasCriticalNu_target :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroStableKeyTableWitnessCorrelationLength
      zeroStableKeyTableWitnessPackage.certificate.predictedExponent :=
  zeroStableKeyTableWitnessPackage.hasCriticalNu_of_bridge
    zeroStableKeyTableWitnessBridge



theorem zeroStableKeyTableWitness_predictedExponent_eq :
    zeroStableKeyTableWitnessPackage.certificate.predictedExponent =
      predictedNu exampleScale 3 := by
  rw [InfiniteTailTableWitnessPackage.certificate_predictedExponent_eq]
  rfl



theorem zeroStableKeyTableWitness_hasCriticalNu_formulaTarget :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroStableKeyTableWitnessCorrelationLength
      (predictedNu exampleScale 3) := by
  simpa [zeroStableKeyTableWitness_predictedExponent_eq] using
    zeroStableKeyTableWitness_hasCriticalNu_target




theorem zeroStableKeyTableWitness_bridge_reparameterized_from_congrTarget :
    zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge
      zeroStableKeyTableWitnessReparameterizedCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      zeroStableKeyTableWitness_predictedExponent_eq
      zeroStableKeyTableWitness_hasCriticalNu_formulaTarget
      toyLinearReparam_leftCritical
      zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq


theorem zeroStableKeyTableWitness_valid_reparameterized_from_congrTarget :
    zeroStableKeyTableWitnessPackage.certificate.Valid
      zeroStableKeyTableWitnessReparameterizedCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      zeroStableKeyTableWitness_predictedExponent_eq
      zeroStableKeyTableWitness_hasCriticalNu_formulaTarget
      toyLinearReparam_leftCritical
      zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq



theorem zeroStableKeyTableWitness_hasCriticalNu_reparameterized_from_congrTarget :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroStableKeyTableWitnessReparameterizedCorrelationLength
      zeroStableKeyTableWitnessPackage.certificate.predictedExponent :=
  (zeroStableKeyTableWitnessPackage
    |>.valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      zeroStableKeyTableWitness_predictedExponent_eq
      zeroStableKeyTableWitness_hasCriticalNu_formulaTarget
      toyLinearReparam_leftCritical
      zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq).hasCriticalNu



theorem zeroStableKeyTableWitness_bridge_reparameterized_from_targetExponent :
    zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge
      zeroStableKeyTableWitnessReparameterizedCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
      zeroStableKeyTableWitness_hasCriticalNu_target
      toyLinearReparam_leftCritical
      zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq



theorem zeroStableKeyTableWitness_valid_reparameterized_from_targetExponent :
    zeroStableKeyTableWitnessPackage.certificate.Valid
      zeroStableKeyTableWitnessReparameterizedCorrelationLength :=
  zeroStableKeyTableWitnessPackage.valid_of_reparameterized_hasCriticalNu_eventually_eq
    zeroStableKeyTableWitness_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq



theorem zeroStableKeyTableWitness_hasCriticalNu_reparameterized_from_targetExponent :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroStableKeyTableWitnessReparameterizedCorrelationLength
      zeroStableKeyTableWitnessPackage.certificate.predictedExponent :=
  zeroStableKeyTableWitnessPackage.hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    zeroStableKeyTableWitness_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq



theorem zeroStableKeyTableWitness_bridge_reparameterized_from_externalBridge :
    zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge
      zeroStableKeyTableWitnessReparameterizedCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
      zeroStableKeyTableWitnessPackage.certificate
      rfl
      zeroStableKeyTableWitnessBridge
      toyLinearReparam_leftCritical
      zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq



theorem zeroStableKeyTableWitness_valid_reparameterized_from_externalBridge :
    zeroStableKeyTableWitnessPackage.certificate.Valid
      zeroStableKeyTableWitnessReparameterizedCorrelationLength :=
  zeroStableKeyTableWitnessPackage.valid_of_reparameterized_rgToExponentBridge_eventually_eq
    zeroStableKeyTableWitnessPackage.certificate
    rfl
    zeroStableKeyTableWitnessBridge
    toyLinearReparam_leftCritical
    zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq



theorem
    zeroStableKeyTableWitness_hasCriticalNu_reparameterized_from_externalBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroStableKeyTableWitnessReparameterizedCorrelationLength
      zeroStableKeyTableWitnessPackage.certificate.predictedExponent :=
  zeroStableKeyTableWitnessPackage.hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    zeroStableKeyTableWitnessPackage.certificate
    rfl
    zeroStableKeyTableWitnessBridge
    toyLinearReparam_leftCritical
    zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq



theorem zeroStableKeyTableWitnessRetargetBridge :
    (zeroStableKeyTableWitnessPackage.certificate.retarget
      (ToyCriticalModel exampleScale 3)).RGToExponentBridge
        zeroStableKeyTableWitnessCorrelationLength := by
  change HasCriticalNu (ToyCriticalModel exampleScale 3)
    zeroStableKeyTableWitnessCorrelationLength
    (zeroStableKeyTableWitnessPackage.certificate.retarget
      (ToyCriticalModel exampleScale 3)).predictedExponent
  simpa using zeroStableKeyTableWitness_hasCriticalNu_target



theorem zeroStableKeyTableWitness_bridge_reparameterized_from_retargetBridge :
    zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge
      zeroStableKeyTableWitnessReparameterizedCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
      zeroStableKeyTableWitnessRetargetBridge
      toyLinearReparam_leftCritical
      zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq



theorem zeroStableKeyTableWitness_valid_reparameterized_from_retargetBridge :
    zeroStableKeyTableWitnessPackage.certificate.Valid
      zeroStableKeyTableWitnessReparameterizedCorrelationLength :=
  zeroStableKeyTableWitnessPackage.valid_of_reparameterized_retargetBridge_eventually_eq
    zeroStableKeyTableWitnessRetargetBridge
    toyLinearReparam_leftCritical
    zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq



theorem zeroStableKeyTableWitness_hasCriticalNu_reparameterized_from_retargetBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroStableKeyTableWitnessReparameterizedCorrelationLength
      zeroStableKeyTableWitnessPackage.certificate.predictedExponent :=
  zeroStableKeyTableWitnessPackage.hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    zeroStableKeyTableWitnessRetargetBridge
    toyLinearReparam_leftCritical
    zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq



noncomputable def zeroTableClosedBallReparameterizedLength (β : ℝ) : ℝ :=
  halfThirdScalingCorrelationLength (toyLinearReparam β)



theorem zeroTableClosedBallReparameterizedLength_eventually_eq :
    ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC
        (Set.Iio (ToyCriticalModel exampleScale 3).betaC),
      zeroTableClosedBallReparameterizedLength β =
        halfThirdScalingCorrelationLength (toyLinearReparam β) :=
  Filter.Eventually.of_forall fun _ => rfl




theorem zeroTableClosedBallRGPackage_hasCriticalNu_target :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (zeroTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent := by
  simpa [zeroTableClosedBallRGPackage_predictedExponent_eq,
    halfThirdScalingRGCertificate_predictedExponent_eq] using
    halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs



theorem zeroTableClosedBallRGPackage_bridge_reparameterized_from_congrTarget :
    (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := zeroTableClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent
    exampleScale
    zeroTableClosedBallRGPackage_predictedExponent_eq
    (by
      simpa [zeroTableClosedBallRGPackage_predictedExponent_eq] using
        zeroTableClosedBallRGPackage_hasCriticalNu_target)
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem zeroTableClosedBallRGPackage_valid_reparameterized_from_congrTarget :
    (zeroTableClosedBallRGPackage.certificate exampleScale).Valid
      zeroTableClosedBallReparameterizedLength := by
  let P := zeroTableClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    exampleScale
    zeroTableClosedBallRGPackage_predictedExponent_eq
    (by
      simpa [zeroTableClosedBallRGPackage_predictedExponent_eq] using
        zeroTableClosedBallRGPackage_hasCriticalNu_target)
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem zeroTableClosedBallRGPackage_hasCriticalNu_reparameterized_from_congrTarget :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
  let P := zeroTableClosedBallRGPackage
  exact
    (P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      exampleScale
      zeroTableClosedBallRGPackage_predictedExponent_eq
      (by
        simpa [zeroTableClosedBallRGPackage_predictedExponent_eq] using
          zeroTableClosedBallRGPackage_hasCriticalNu_target)
      toyLinearReparam_leftCritical
      zeroTableClosedBallReparameterizedLength_eventually_eq).hasCriticalNu



theorem zeroTableClosedBallRGPackage_bridge_reparameterized :
    (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := zeroTableClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    zeroTableClosedBallRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq




theorem zeroTableClosedBallRGPackage_valid_reparameterized :
    (zeroTableClosedBallRGPackage.certificate exampleScale).Valid
      zeroTableClosedBallReparameterizedLength := by
  let P := zeroTableClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    zeroTableClosedBallRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem zeroTableClosedBallRGPackage_hasCriticalNu_reparameterized :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
  let P := zeroTableClosedBallRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    zeroTableClosedBallRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem zeroTableClosedBallRGPackageBridge :
    (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge
      halfThirdScalingCorrelationLength := by
  change HasCriticalNu (ToyCriticalModel exampleScale 3)
    halfThirdScalingCorrelationLength
    (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent
  exact zeroTableClosedBallRGPackage_hasCriticalNu_target



theorem zeroTableClosedBallRGPackage_bridge_reparameterized_from_externalBridge :
    (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := zeroTableClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    zeroTableClosedBallRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq




theorem zeroTableClosedBallRGPackage_valid_reparameterized_from_externalBridge :
    (zeroTableClosedBallRGPackage.certificate exampleScale).Valid
      zeroTableClosedBallReparameterizedLength := by
  let P := zeroTableClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    zeroTableClosedBallRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    zeroTableClosedBallRGPackage_hasCriticalNu_reparameterized_from_externalBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
  let P := zeroTableClosedBallRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    zeroTableClosedBallRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem zeroTableClosedBallRGPackageRetargetBridge :
    ((zeroTableClosedBallRGPackage.certificate exampleScale).retarget
      (ToyCriticalModel exampleScale 3)).RGToExponentBridge
        halfThirdScalingCorrelationLength := by
  change HasCriticalNu (ToyCriticalModel exampleScale 3)
    halfThirdScalingCorrelationLength
    ((zeroTableClosedBallRGPackage.certificate exampleScale).retarget
      (ToyCriticalModel exampleScale 3)).predictedExponent
  simpa using zeroTableClosedBallRGPackage_hasCriticalNu_target



theorem zeroTableClosedBallRGPackage_bridge_reparameterized_from_retargetBridge :
    (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := zeroTableClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    zeroTableClosedBallRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq




theorem zeroTableClosedBallRGPackage_valid_reparameterized_from_retargetBridge :
    (zeroTableClosedBallRGPackage.certificate exampleScale).Valid
      zeroTableClosedBallReparameterizedLength := by
  let P := zeroTableClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    zeroTableClosedBallRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    zeroTableClosedBallRGPackage_hasCriticalNu_reparameterized_from_retargetBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
  let P := zeroTableClosedBallRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    zeroTableClosedBallRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq




theorem generatedReplacedTCBRGPackage_hasCriticalNu_target :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent := by
  simpa [
    generatedStableKeyReplacedTableClosedBallRGPackage_predictedExponent_eq,
    halfThirdScalingRGCertificate_predictedExponent_eq] using
    halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs



theorem generatedReplacedTCBRGPackage_bridge_reparameterized_from_congrTarget :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := generatedStableKeyReplacedTableClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_predictedExponent_eq
    (by
      simpa [
        generatedStableKeyReplacedTableClosedBallRGPackage_predictedExponent_eq]
        using generatedReplacedTCBRGPackage_hasCriticalNu_target)
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem generatedReplacedTCBRGPackage_valid_reparameterized_from_congrTarget :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
  let P := generatedStableKeyReplacedTableClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_predictedExponent_eq
    (by
      simpa [
        generatedStableKeyReplacedTableClosedBallRGPackage_predictedExponent_eq]
        using generatedReplacedTCBRGPackage_hasCriticalNu_target)
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem generatedReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_congrTarget :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent := by
  let P := generatedStableKeyReplacedTableClosedBallRGPackage
  exact
    (P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      exampleScale
      generatedStableKeyReplacedTableClosedBallRGPackage_predictedExponent_eq
      (by
        simpa [
          generatedStableKeyReplacedTableClosedBallRGPackage_predictedExponent_eq]
          using generatedReplacedTCBRGPackage_hasCriticalNu_target)
      toyLinearReparam_leftCritical
      zeroTableClosedBallReparameterizedLength_eventually_eq).hasCriticalNu



theorem generatedReplacedTCBRGPackage_bridge_reparameterized :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := generatedStableKeyReplacedTableClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    generatedReplacedTCBRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq




theorem generatedReplacedTCBRGPackage_valid_reparameterized :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
  let P := generatedStableKeyReplacedTableClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    generatedReplacedTCBRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem generatedReplacedTCBRGPackage_hasCriticalNu_reparameterized :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent := by
  let P := generatedStableKeyReplacedTableClosedBallRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    generatedReplacedTCBRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem generatedReplacedTCBRGPackageBridge :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
  change HasCriticalNu (ToyCriticalModel exampleScale 3)
    halfThirdScalingCorrelationLength
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).predictedExponent
  exact generatedReplacedTCBRGPackage_hasCriticalNu_target




theorem generatedReplacedTCBRGPackage_bridge_reparameterized_from_externalBridge :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := generatedStableKeyReplacedTableClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    generatedReplacedTCBRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq




theorem generatedReplacedTCBRGPackage_valid_reparameterized_from_externalBridge :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
  let P := generatedStableKeyReplacedTableClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    generatedReplacedTCBRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    generatedReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_externalBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent := by
  let P := generatedStableKeyReplacedTableClosedBallRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    generatedReplacedTCBRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq




theorem generatedReplacedTCBRGPackageRetargetBridge :
    ((generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).retarget
        (ToyCriticalModel exampleScale 3)).RGToExponentBridge
          halfThirdScalingCorrelationLength := by
  change HasCriticalNu (ToyCriticalModel exampleScale 3)
    halfThirdScalingCorrelationLength
    ((generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).retarget
        (ToyCriticalModel exampleScale 3)).predictedExponent
  simpa using generatedReplacedTCBRGPackage_hasCriticalNu_target




theorem generatedReplacedTCBRGPackage_bridge_reparameterized_from_retargetBridge :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := generatedStableKeyReplacedTableClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    generatedReplacedTCBRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq




theorem generatedReplacedTCBRGPackage_valid_reparameterized_from_retargetBridge :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
  let P := generatedStableKeyReplacedTableClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    generatedReplacedTCBRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    generatedReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_retargetBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent := by
  let P := generatedStableKeyReplacedTableClosedBallRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    generatedReplacedTCBRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq




theorem genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_target :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent := by
  simpa [
    genMinCubicKeyReplacedTableClosedBallRGPackage_predictedExponent_eq,
    halfThirdScalingRGCertificate_predictedExponent_eq] using
    halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs




theorem genMinCubicKeyReplacedTCBRGPackage_bridge_reparameterized :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := genMinCubicKeyReplacedTableClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem genMinCubicKeyReplacedTCBRGPackage_valid_reparameterized :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
  let P := genMinCubicKeyReplacedTableClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_reparameterized :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent := by
  let P := genMinCubicKeyReplacedTableClosedBallRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    genMinCubicKeyReplacedTCBRGPackage_bridge_reparameterized_from_congrTarget :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := genMinCubicKeyReplacedTableClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent
    exampleScale
    genMinCubicKeyReplacedTableClosedBallRGPackage_predictedExponent_eq
    (by
      simpa [
        genMinCubicKeyReplacedTableClosedBallRGPackage_predictedExponent_eq]
        using genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_target)
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    genMinCubicKeyReplacedTCBRGPackage_valid_reparameterized_from_congrTarget :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
  let P := genMinCubicKeyReplacedTableClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    exampleScale
    genMinCubicKeyReplacedTableClosedBallRGPackage_predictedExponent_eq
    (by
      simpa [
        genMinCubicKeyReplacedTableClosedBallRGPackage_predictedExponent_eq]
        using genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_target)
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_congrTarget :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent := by
  let P := genMinCubicKeyReplacedTableClosedBallRGPackage
  exact
    (P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      exampleScale
      genMinCubicKeyReplacedTableClosedBallRGPackage_predictedExponent_eq
      (by
        simpa [
          genMinCubicKeyReplacedTableClosedBallRGPackage_predictedExponent_eq]
          using genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_target)
      toyLinearReparam_leftCritical
      zeroTableClosedBallReparameterizedLength_eventually_eq).hasCriticalNu



theorem genMinCubicKeyReplacedTCBRGPackageBridge :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
  change HasCriticalNu (ToyCriticalModel exampleScale 3)
    halfThirdScalingCorrelationLength
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).predictedExponent
  exact genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_target



theorem
    genMinCubicKeyReplacedTCBRGPackage_bridge_reparameterized_from_externalBridge :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := genMinCubicKeyReplacedTableClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    genMinCubicKeyReplacedTCBRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    genMinCubicKeyReplacedTCBRGPackage_valid_reparameterized_from_externalBridge :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
  let P := genMinCubicKeyReplacedTableClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    genMinCubicKeyReplacedTCBRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_externalBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent := by
  let P := genMinCubicKeyReplacedTableClosedBallRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    genMinCubicKeyReplacedTCBRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem genMinCubicKeyReplacedTCBRGPackageRetargetBridge :
    ((genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).retarget
        (ToyCriticalModel exampleScale 3)).RGToExponentBridge
          halfThirdScalingCorrelationLength := by
  change HasCriticalNu (ToyCriticalModel exampleScale 3)
    halfThirdScalingCorrelationLength
    ((genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).retarget
        (ToyCriticalModel exampleScale 3)).predictedExponent
  simpa using genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_target



theorem
    genMinCubicKeyReplacedTCBRGPackage_bridge_reparameterized_from_retargetBridge :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := genMinCubicKeyReplacedTableClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    genMinCubicKeyReplacedTCBRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    genMinCubicKeyReplacedTCBRGPackage_valid_reparameterized_from_retargetBridge :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
  let P := genMinCubicKeyReplacedTableClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    genMinCubicKeyReplacedTCBRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_retargetBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent := by
  let P := genMinCubicKeyReplacedTableClosedBallRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    genMinCubicKeyReplacedTCBRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq




theorem genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_target :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
  simpa [
    genBoundedCaseReplacedPackage_predictedExponent_eq,
    halfThirdScalingRGCertificate_predictedExponent_eq] using
    halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs




theorem genBoundedCaseReplacedTCBRGPackage_bridge_reparameterized :
    (genBoundedCaseReplacedPackage.certificate
      exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := genBoundedCaseReplacedPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem genBoundedCaseReplacedTCBRGPackage_valid_reparameterized :
    (genBoundedCaseReplacedPackage.certificate exampleScale).Valid
      zeroTableClosedBallReparameterizedLength := by
  let P := genBoundedCaseReplacedPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_reparameterized :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
  let P := genBoundedCaseReplacedPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    genBoundedCaseReplacedTCBRGPackage_bridge_reparameterized_from_congrTarget :
    (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := genBoundedCaseReplacedPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent
    exampleScale
    genBoundedCaseReplacedPackage_predictedExponent_eq
    (by
      simpa [genBoundedCaseReplacedPackage_predictedExponent_eq]
        using genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_target)
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    genBoundedCaseReplacedTCBRGPackage_valid_reparameterized_from_congrTarget :
    (genBoundedCaseReplacedPackage.certificate exampleScale).Valid
      zeroTableClosedBallReparameterizedLength := by
  let P := genBoundedCaseReplacedPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    exampleScale
    genBoundedCaseReplacedPackage_predictedExponent_eq
    (by
      simpa [genBoundedCaseReplacedPackage_predictedExponent_eq]
        using genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_target)
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_congrTarget :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
  let P := genBoundedCaseReplacedPackage
  exact
    (P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      exampleScale
      genBoundedCaseReplacedPackage_predictedExponent_eq
      (by
        simpa [genBoundedCaseReplacedPackage_predictedExponent_eq]
          using genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_target)
      toyLinearReparam_leftCritical
      zeroTableClosedBallReparameterizedLength_eventually_eq).hasCriticalNu



theorem genBoundedCaseReplacedTCBRGPackageBridge :
    (genBoundedCaseReplacedPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
  change HasCriticalNu (ToyCriticalModel exampleScale 3)
    halfThirdScalingCorrelationLength
    (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent
  exact genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_target



theorem
    genBoundedCaseReplacedTCBRGPackage_bridge_reparameterized_from_externalBridge :
    (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := genBoundedCaseReplacedPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    genBoundedCaseReplacedTCBRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    genBoundedCaseReplacedTCBRGPackage_valid_reparameterized_from_externalBridge :
    (genBoundedCaseReplacedPackage.certificate exampleScale).Valid
      zeroTableClosedBallReparameterizedLength := by
  let P := genBoundedCaseReplacedPackage
  exact P.certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    genBoundedCaseReplacedTCBRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_externalBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
  let P := genBoundedCaseReplacedPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    genBoundedCaseReplacedTCBRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem genBoundedCaseReplacedTCBRGPackageRetargetBridge :
    ((genBoundedCaseReplacedPackage.certificate exampleScale).retarget
      (ToyCriticalModel exampleScale 3)).RGToExponentBridge
        halfThirdScalingCorrelationLength := by
  change HasCriticalNu (ToyCriticalModel exampleScale 3)
    halfThirdScalingCorrelationLength
    ((genBoundedCaseReplacedPackage.certificate exampleScale).retarget
      (ToyCriticalModel exampleScale 3)).predictedExponent
  simpa using genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_target



theorem
    genBoundedCaseReplacedTCBRGPackage_bridge_reparameterized_from_retargetBridge :
    (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := genBoundedCaseReplacedPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    genBoundedCaseReplacedTCBRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    genBoundedCaseReplacedTCBRGPackage_valid_reparameterized_from_retargetBridge :
    (genBoundedCaseReplacedPackage.certificate exampleScale).Valid
      zeroTableClosedBallReparameterizedLength := by
  let P := genBoundedCaseReplacedPackage
  exact P.certificate_valid_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    genBoundedCaseReplacedTCBRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_retargetBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
  let P := genBoundedCaseReplacedPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    genBoundedCaseReplacedTCBRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq




theorem genCubicClassReplacedTCBRGPackage_hasCriticalNu_target :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
  simpa [
    genCubicClassReplacedPackage_predictedExponent_eq,
    halfThirdScalingRGCertificate_predictedExponent_eq] using
    halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs




theorem genCubicClassReplacedTCBRGPackage_bridge_reparameterized :
    (genCubicClassReplacedPackage.certificate
      exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := genCubicClassReplacedPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    genCubicClassReplacedTCBRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem genCubicClassReplacedTCBRGPackage_valid_reparameterized :
    (genCubicClassReplacedPackage.certificate exampleScale).Valid
      zeroTableClosedBallReparameterizedLength := by
  let P := genCubicClassReplacedPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    genCubicClassReplacedTCBRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem genCubicClassReplacedTCBRGPackage_hasCriticalNu_reparameterized :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
  let P := genCubicClassReplacedPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    genCubicClassReplacedTCBRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    genCubicClassReplacedTCBRGPackage_bridge_reparameterized_from_congrTarget :
    (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := genCubicClassReplacedPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent
    exampleScale
    genCubicClassReplacedPackage_predictedExponent_eq
    (by
      simpa [genCubicClassReplacedPackage_predictedExponent_eq]
        using genCubicClassReplacedTCBRGPackage_hasCriticalNu_target)
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    genCubicClassReplacedTCBRGPackage_valid_reparameterized_from_congrTarget :
    (genCubicClassReplacedPackage.certificate exampleScale).Valid
      zeroTableClosedBallReparameterizedLength := by
  let P := genCubicClassReplacedPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    exampleScale
    genCubicClassReplacedPackage_predictedExponent_eq
    (by
      simpa [genCubicClassReplacedPackage_predictedExponent_eq]
        using genCubicClassReplacedTCBRGPackage_hasCriticalNu_target)
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    genCubicClassReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_congrTarget :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
  let P := genCubicClassReplacedPackage
  exact
    (P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      exampleScale
      genCubicClassReplacedPackage_predictedExponent_eq
      (by
        simpa [genCubicClassReplacedPackage_predictedExponent_eq]
          using genCubicClassReplacedTCBRGPackage_hasCriticalNu_target)
      toyLinearReparam_leftCritical
      zeroTableClosedBallReparameterizedLength_eventually_eq).hasCriticalNu



theorem genCubicClassReplacedTCBRGPackageBridge :
    (genCubicClassReplacedPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
  change HasCriticalNu (ToyCriticalModel exampleScale 3)
    halfThirdScalingCorrelationLength
    (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent
  exact genCubicClassReplacedTCBRGPackage_hasCriticalNu_target



theorem
    genCubicClassReplacedTCBRGPackage_bridge_reparameterized_from_externalBridge :
    (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := genCubicClassReplacedPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    genCubicClassReplacedTCBRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    genCubicClassReplacedTCBRGPackage_valid_reparameterized_from_externalBridge :
    (genCubicClassReplacedPackage.certificate exampleScale).Valid
      zeroTableClosedBallReparameterizedLength := by
  let P := genCubicClassReplacedPackage
  exact P.certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    genCubicClassReplacedTCBRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    genCubicClassReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_externalBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
  let P := genCubicClassReplacedPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    genCubicClassReplacedTCBRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem genCubicClassReplacedTCBRGPackageRetargetBridge :
    ((genCubicClassReplacedPackage.certificate exampleScale).retarget
      (ToyCriticalModel exampleScale 3)).RGToExponentBridge
        halfThirdScalingCorrelationLength := by
  change HasCriticalNu (ToyCriticalModel exampleScale 3)
    halfThirdScalingCorrelationLength
    ((genCubicClassReplacedPackage.certificate exampleScale).retarget
      (ToyCriticalModel exampleScale 3)).predictedExponent
  simpa using genCubicClassReplacedTCBRGPackage_hasCriticalNu_target



theorem
    genCubicClassReplacedTCBRGPackage_bridge_reparameterized_from_retargetBridge :
    (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := genCubicClassReplacedPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    genCubicClassReplacedTCBRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    genCubicClassReplacedTCBRGPackage_valid_reparameterized_from_retargetBridge :
    (genCubicClassReplacedPackage.certificate exampleScale).Valid
      zeroTableClosedBallReparameterizedLength := by
  let P := genCubicClassReplacedPackage
  exact P.certificate_valid_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    genCubicClassReplacedTCBRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq



theorem
    genCubicClassReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_retargetBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
  let P := genCubicClassReplacedPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    genCubicClassReplacedTCBRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq

end PackageReparameterizationBridgeExample
end Exact3D
end StatMech

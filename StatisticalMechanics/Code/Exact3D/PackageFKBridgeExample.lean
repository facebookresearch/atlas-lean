/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.CriticalExponentCriteria
import Code.Exact3D.FKFinitePlusTailBridge
import Code.Exact3D.FKTableClosedBallBridge
import Code.Exact3D.FKWitnessBridge
import Code.Exact3D.FinitePlusTailContractionExample
import Code.Exact3D.FiniteWitnessPackageExample
import Code.Exact3D.InfiniteTailWitnessPackageExample
import Code.Exact3D.PackageExponentMatchingExample









namespace StatMech
namespace Exact3D
namespace PackageFKBridgeExample

open FiniteWitnessPackageExample
open FinitePlusTailContractionExample
open InfiniteTailWitnessPackageExample
open PackageExponentMatchingExample

variable
  (TFKM :
    FKMassPowerLawToIsingAnalyticRGToExponentTarget
      (halfThirdScalingRGCertificate.retarget Ising3DModel))



noncomputable def blockRGFKToyCorrelationLength (p : ℝ) : ℝ :=
  Real.exp
    (-((halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent) *
      Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))


theorem blockRGFKToyCorrelationLength_exact_power :
    ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))),
      blockRGFKToyCorrelationLength p =
        Real.exp
          (-((halfThirdScalingRGCertificate.retarget
                Ising3DModel).predictedExponent) *
            Real.log
              ((ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))).betaC -
                p)) :=
  Filter.Eventually.of_forall fun _ => rfl



theorem blockRGFKToy_hasCriticalNu :
    HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
      blockRGFKToyCorrelationLength
      (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent :=
  hasCriticalNu_of_eventually_exact_power
    (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
    blockRGFKToyCorrelationLength
    (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent
    blockRGFKToyCorrelationLength_exact_power



noncomputable def blockRGFKComposedIsingCorrelationLength (β : ℝ) : ℝ :=
  blockRGFKToyCorrelationLength (IsingFK.pOfBeta β)



theorem blockRGFKComposedIsingCorrelationLength_eventually_eq :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      blockRGFKComposedIsingCorrelationLength β =
        blockRGFKToyCorrelationLength (IsingFK.pOfBeta β) :=
  Filter.Eventually.of_forall fun _ => rfl

section FiniteWitnessExamples

open FiniteWitnessPackage



theorem contributionSplitWitnessPackage_bridge_from_fk_pOfBeta_congr_pred :
    ((contributionSplitWitnessPackage.retarget
      Ising3DModel).certificate).RGToExponentBridge
      blockRGFKComposedIsingCorrelationLength :=
  rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (contributionSplitWitnessPackage.retarget Ising3DModel)
    contributionSplitWitnessPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem contributionSplitWitnessPackage_bridge_from_fkPowerTarget_congr_pred :
    ((contributionSplitWitnessPackage.retarget
      Ising3DModel).certificate).RGToExponentBridge
      TFKM.isingCorrelationLength :=
  rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent
    (contributionSplitWitnessPackage.retarget Ising3DModel)
    contributionSplitWitnessPackage_ising_predictedExponent_eq_rg
    TFKM.toFKPowerLawTarget



theorem contributionSplitWitnessPackage_valid_from_fkPowerTarget_congr_pred :
    (contributionSplitWitnessPackage.retarget Ising3DModel).certificate.Valid
      TFKM.isingCorrelationLength :=
  valid_of_fkPowerLawTarget_congr_predictedExponent
    (contributionSplitWitnessPackage.retarget Ising3DModel)
    contributionSplitWitnessPackage_ising_predictedExponent_eq_rg
    TFKM.toFKPowerLawTarget



theorem
    contributionSplitWitnessPackage_hasCriticalNu_from_fkPowerTarget_congr_pred :
    HasCriticalNu Ising3DModel TFKM.isingCorrelationLength
      ((contributionSplitWitnessPackage.retarget
        Ising3DModel).certificate).predictedExponent :=
  hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent
    (contributionSplitWitnessPackage.retarget Ising3DModel)
    contributionSplitWitnessPackage_ising_predictedExponent_eq_rg
    TFKM.toFKPowerLawTarget



theorem contributionSplitWitnessPackage_bridge_from_fkMassPowerTarget_congr_pred :
    ((contributionSplitWitnessPackage.retarget
      Ising3DModel).certificate).RGToExponentBridge
      TFKM.isingCorrelationLength :=
  rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent
    (contributionSplitWitnessPackage.retarget Ising3DModel)
    contributionSplitWitnessPackage_ising_predictedExponent_eq_rg
    TFKM



theorem contributionSplitWitnessPackage_valid_from_fkMassPowerTarget_congr_pred :
    (contributionSplitWitnessPackage.retarget Ising3DModel).certificate.Valid
      TFKM.isingCorrelationLength :=
  valid_of_fkMassPowerLawTarget_congr_predictedExponent
    (contributionSplitWitnessPackage.retarget Ising3DModel)
    contributionSplitWitnessPackage_ising_predictedExponent_eq_rg
    TFKM



theorem
    contributionSplitWitnessPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred :
    HasCriticalNu Ising3DModel TFKM.isingCorrelationLength
      ((contributionSplitWitnessPackage.retarget
        Ising3DModel).certificate).predictedExponent :=
  hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent
    (contributionSplitWitnessPackage.retarget Ising3DModel)
    contributionSplitWitnessPackage_ising_predictedExponent_eq_rg
    TFKM



theorem contributionSplitWitnessPackage_valid_from_fk_pOfBeta_congr_pred :
    (contributionSplitWitnessPackage.retarget Ising3DModel).certificate.Valid
      blockRGFKComposedIsingCorrelationLength :=
  valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (contributionSplitWitnessPackage.retarget Ising3DModel)
    contributionSplitWitnessPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem contributionSplitWitnessPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred :
    HasCriticalNu Ising3DModel
      blockRGFKComposedIsingCorrelationLength
      ((contributionSplitWitnessPackage.retarget
        Ising3DModel).certificate).predictedExponent :=
  hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (contributionSplitWitnessPackage.retarget Ising3DModel)
    contributionSplitWitnessPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq

end FiniteWitnessExamples

section InfiniteWitnessExamples

open InfiniteTailWitnessPackage



theorem geometricTailWitnessPackage_bridge_from_fk_pOfBeta_congr_pred :
    ((geometricTailWitnessPackage.retarget
      Ising3DModel).certificate).RGToExponentBridge
      blockRGFKComposedIsingCorrelationLength :=
  rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (geometricTailWitnessPackage.retarget Ising3DModel)
    geometricTailWitnessPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem geometricTailWitnessPackage_valid_from_fk_pOfBeta_congr_pred :
    (geometricTailWitnessPackage.retarget Ising3DModel).certificate.Valid
      blockRGFKComposedIsingCorrelationLength :=
  valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (geometricTailWitnessPackage.retarget Ising3DModel)
    geometricTailWitnessPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem geometricTailWitnessPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred :
    HasCriticalNu Ising3DModel
      blockRGFKComposedIsingCorrelationLength
      ((geometricTailWitnessPackage.retarget
        Ising3DModel).certificate).predictedExponent :=
  hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (geometricTailWitnessPackage.retarget Ising3DModel)
    geometricTailWitnessPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem geometricTailWitnessPackage_bridge_from_fkPowerTarget_congr_pred :
    ((geometricTailWitnessPackage.retarget
      Ising3DModel).certificate).RGToExponentBridge
      TFKM.isingCorrelationLength :=
  rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent
    (geometricTailWitnessPackage.retarget Ising3DModel)
    geometricTailWitnessPackage_ising_predictedExponent_eq_rg
    TFKM.toFKPowerLawTarget



theorem geometricTailWitnessPackage_valid_from_fkPowerTarget_congr_pred :
    (geometricTailWitnessPackage.retarget Ising3DModel).certificate.Valid
      TFKM.isingCorrelationLength :=
  valid_of_fkPowerLawTarget_congr_predictedExponent
    (geometricTailWitnessPackage.retarget Ising3DModel)
    geometricTailWitnessPackage_ising_predictedExponent_eq_rg
    TFKM.toFKPowerLawTarget



theorem geometricTailWitnessPackage_hasCriticalNu_from_fkPowerTarget_congr_pred :
    HasCriticalNu Ising3DModel TFKM.isingCorrelationLength
      ((geometricTailWitnessPackage.retarget
        Ising3DModel).certificate).predictedExponent :=
  hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent
    (geometricTailWitnessPackage.retarget Ising3DModel)
    geometricTailWitnessPackage_ising_predictedExponent_eq_rg
    TFKM.toFKPowerLawTarget



theorem geometricTailWitnessPackage_bridge_from_fkMassPowerTarget_congr_pred :
    ((geometricTailWitnessPackage.retarget
      Ising3DModel).certificate).RGToExponentBridge
      TFKM.isingCorrelationLength :=
  rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent
    (geometricTailWitnessPackage.retarget Ising3DModel)
    geometricTailWitnessPackage_ising_predictedExponent_eq_rg
    TFKM



theorem geometricTailWitnessPackage_valid_from_fkMassPowerTarget_congr_pred :
    (geometricTailWitnessPackage.retarget Ising3DModel).certificate.Valid
      TFKM.isingCorrelationLength :=
  valid_of_fkMassPowerLawTarget_congr_predictedExponent
    (geometricTailWitnessPackage.retarget Ising3DModel)
    geometricTailWitnessPackage_ising_predictedExponent_eq_rg
    TFKM



theorem
    geometricTailWitnessPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred :
    HasCriticalNu Ising3DModel TFKM.isingCorrelationLength
      ((geometricTailWitnessPackage.retarget
        Ising3DModel).certificate).predictedExponent :=
  hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent
    (geometricTailWitnessPackage.retarget Ising3DModel)
    geometricTailWitnessPackage_ising_predictedExponent_eq_rg
    TFKM

end InfiniteWitnessExamples

section TableWitnessExamples

open InfiniteTailTableWitnessPackage



theorem zeroStableKeyTableWitnessPackage_bridge_from_fk_pOfBeta_congr_pred :
    ((zeroTableClosedBallRGPackage.tableWitness.retarget
      Ising3DModel).certificate).RGToExponentBridge
      blockRGFKComposedIsingCorrelationLength :=
  rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel)
    zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem zeroStableKeyTableWitnessPackage_valid_from_fk_pOfBeta_congr_pred :
    (zeroTableClosedBallRGPackage.tableWitness.retarget
      Ising3DModel).certificate.Valid blockRGFKComposedIsingCorrelationLength :=
  valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel)
    zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem zeroStableKeyTableWitnessPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred :
    HasCriticalNu Ising3DModel
      blockRGFKComposedIsingCorrelationLength
      ((zeroTableClosedBallRGPackage.tableWitness.retarget
        Ising3DModel).certificate).predictedExponent :=
  hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel)
    zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem zeroStableKeyTableWitnessPackage_bridge_from_fkPowerTarget_congr_pred :
    ((zeroTableClosedBallRGPackage.tableWitness.retarget
      Ising3DModel).certificate).RGToExponentBridge
      TFKM.isingCorrelationLength :=
  rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel)
    zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg
    TFKM.toFKPowerLawTarget



theorem zeroStableKeyTableWitnessPackage_valid_from_fkPowerTarget_congr_pred :
    (zeroTableClosedBallRGPackage.tableWitness.retarget
      Ising3DModel).certificate.Valid TFKM.isingCorrelationLength :=
  valid_of_fkPowerLawTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel)
    zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg
    TFKM.toFKPowerLawTarget



theorem zeroStableKeyTableWitnessPackage_hasCriticalNu_from_fkPowerTarget_congr_pred :
    HasCriticalNu Ising3DModel TFKM.isingCorrelationLength
      ((zeroTableClosedBallRGPackage.tableWitness.retarget
        Ising3DModel).certificate).predictedExponent :=
  hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel)
    zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg
    TFKM.toFKPowerLawTarget



theorem zeroStableKeyTableWitnessPackage_bridge_from_fkMassPowerTarget_congr_pred :
    ((zeroTableClosedBallRGPackage.tableWitness.retarget
      Ising3DModel).certificate).RGToExponentBridge
      TFKM.isingCorrelationLength :=
  rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel)
    zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg
    TFKM



theorem zeroStableKeyTableWitnessPackage_valid_from_fkMassPowerTarget_congr_pred :
    (zeroTableClosedBallRGPackage.tableWitness.retarget
      Ising3DModel).certificate.Valid TFKM.isingCorrelationLength :=
  valid_of_fkMassPowerLawTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel)
    zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg
    TFKM



theorem
    zeroStableKeyTableWitnessPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred :
    HasCriticalNu Ising3DModel TFKM.isingCorrelationLength
      ((zeroTableClosedBallRGPackage.tableWitness.retarget
        Ising3DModel).certificate).predictedExponent :=
  hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel)
    zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg
    TFKM

end TableWitnessExamples

section HyperbolicExamples

open FinitePlusTailHyperbolicSplitting



theorem halfThirdScalingHyperbolic_bridge_from_fk_pOfBeta_congr_pred :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      blockRGFKComposedIsingCorrelationLength :=
  certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem halfThirdScalingHyperbolic_bridge_from_fkMassTarget_congr_pred :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      TFKM.isingCorrelationLength :=
  certificate_rgToExponentBridge_of_fkMassTarget_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg
    TFKM.toFKMassTarget



theorem halfThirdScalingHyperbolic_valid_from_fkMassTarget_congr_pred :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid
      TFKM.isingCorrelationLength :=
  certificate_valid_of_fkMassTarget_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg
    TFKM.toFKMassTarget



theorem halfThirdScalingHyperbolic_hasCriticalNu_from_fkMassTarget_congr_pred :
    HasCriticalNu Ising3DModel
      TFKM.isingCorrelationLength
      (halfThirdScalingHyperbolicSplitting.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  certificate_hasCriticalNu_of_fkMassTarget_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg
    TFKM.toFKMassTarget



theorem halfThirdScalingHyperbolic_valid_from_fk_pOfBeta_congr_pred :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid
      blockRGFKComposedIsingCorrelationLength :=
  certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem halfThirdScalingHyperbolic_hasCriticalNu_from_fk_pOfBeta_congr_pred :
    HasCriticalNu Ising3DModel
      blockRGFKComposedIsingCorrelationLength
      (halfThirdScalingHyperbolicSplitting.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq

end HyperbolicExamples

section BlockRGExamples

open FinitePlusTailBlockRGPackage



theorem halfThirdScalingBlockRGPackage_bridge_from_fk_pOfBeta_congr_pred :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      blockRGFKComposedIsingCorrelationLength :=
  certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingBlockRGPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem halfThirdScalingBlockRGPackage_valid_from_fk_pOfBeta_congr_pred :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid
      blockRGFKComposedIsingCorrelationLength :=
  certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingBlockRGPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem halfThirdScalingBlockRGPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred :
    HasCriticalNu Ising3DModel
      blockRGFKComposedIsingCorrelationLength
      (halfThirdScalingBlockRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingBlockRGPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq

end BlockRGExamples

section ClosedBallExamples

open FinitePlusTailClosedBallRGPackage



theorem halfThirdScalingClosedBall_bridge_from_fk_pOfBeta_congr_pred :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      blockRGFKComposedIsingCorrelationLength :=
  certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingClosedBall_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem halfThirdScalingClosedBall_valid_from_fk_pOfBeta_congr_pred :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid
      blockRGFKComposedIsingCorrelationLength :=
  certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingClosedBall_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem halfThirdScalingClosedBall_hasCriticalNu_from_fk_pOfBeta_congr_pred :
    HasCriticalNu Ising3DModel
      blockRGFKComposedIsingCorrelationLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingClosedBall_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq

set_option linter.style.longLine false in


theorem halfThirdScalingClosedBall_hasCriticalNu_from_fkMassPowerTarget_congr_pred :
    HasCriticalNu Ising3DModel TFKM.isingCorrelationLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  certificate_hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingClosedBall_ising_predictedExponent_eq_rg
    TFKM

end ClosedBallExamples

section TableClosedBallExamples

open InfiniteTailTableClosedBallRGPackage



theorem zeroTableClosedBallRGPackage_bridge_from_fk_pOfBeta_congr_pred :
    ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
      exampleScale).RGToExponentBridge
      blockRGFKComposedIsingCorrelationLength :=
  certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem zeroTableClosedBallRGPackage_valid_from_fk_pOfBeta_congr_pred :
    ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
      exampleScale).Valid blockRGFKComposedIsingCorrelationLength :=
  certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem zeroTableClosedBallRGPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred :
    HasCriticalNu Ising3DModel
      blockRGFKComposedIsingCorrelationLength
      ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
        exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem zeroTableClosedBallRGPackage_valid_from_fkMassPowerTarget_congr_pred :
    ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
      exampleScale).Valid TFKM.isingCorrelationLength :=
  certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TFKM



theorem zeroTableClosedBallRGPackage_bridge_from_fkMassPowerTarget_congr_pred :
    ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
      exampleScale).RGToExponentBridge TFKM.isingCorrelationLength :=
  certificate_rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TFKM



theorem
    zeroTableClosedBallRGPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred :
    HasCriticalNu Ising3DModel TFKM.isingCorrelationLength
      ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
        exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TFKM



theorem
    generatedReplacedTCBRGPackage_bridge_from_fk_pOfBeta_congr_pred :
    ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      blockRGFKComposedIsingCorrelationLength :=
  certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem
    generatedReplacedTCBRGPackage_valid_from_fk_pOfBeta_congr_pred :
    ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).Valid
      blockRGFKComposedIsingCorrelationLength :=
  certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem
    generatedReplacedTCBRGPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred :
    HasCriticalNu Ising3DModel
      blockRGFKComposedIsingCorrelationLength
      ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem
    generatedReplacedTCBRGPackage_valid_from_fkMassPowerTarget_congr_pred :
    ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).Valid TFKM.isingCorrelationLength :=
  certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent
    (generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TFKM



theorem
    generatedReplacedTCBRGPackage_bridge_from_fkMassPowerTarget_congr_pred :
    ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      TFKM.isingCorrelationLength :=
  certificate_rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent
    (generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TFKM



theorem
    generatedReplacedTCBRGPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred :
    HasCriticalNu Ising3DModel TFKM.isingCorrelationLength
      ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent
    (generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TFKM



theorem
    genMinCubicKeyReplacedPackage_bridge_from_fk_pOfBeta_congr_pred :
    ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      blockRGFKComposedIsingCorrelationLength :=
  certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem
    genMinCubicKeyReplacedPackage_valid_from_fk_pOfBeta_congr_pred :
    ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).Valid
      blockRGFKComposedIsingCorrelationLength :=
  certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq




theorem
    genMinCubicKeyReplacedPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred :
    HasCriticalNu Ising3DModel
      blockRGFKComposedIsingCorrelationLength
      ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem
    genMinCubicKeyReplacedPackage_bridge_from_fkMassPowerTarget_congr_pred :
    ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      TFKM.isingCorrelationLength :=
  certificate_rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent
    (genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg
    TFKM



theorem
    genMinCubicKeyReplacedPackage_valid_from_fkMassPowerTarget_congr_pred :
    ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).Valid TFKM.isingCorrelationLength :=
  certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent
    (genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg
    TFKM




theorem
    genMinCubicKeyReplacedPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred :
    HasCriticalNu Ising3DModel TFKM.isingCorrelationLength
      ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent
    (genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg
    TFKM



theorem
    genBoundedCaseReplacedPackage_bridge_from_fk_pOfBeta_congr_pred :
    ((genBoundedCaseReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      blockRGFKComposedIsingCorrelationLength :=
  certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (genBoundedCaseReplacedPackage.retarget Ising3DModel)
    exampleScale
    genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem
    genBoundedCaseReplacedPackage_valid_from_fk_pOfBeta_congr_pred :
    ((genBoundedCaseReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).Valid
      blockRGFKComposedIsingCorrelationLength :=
  certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (genBoundedCaseReplacedPackage.retarget Ising3DModel)
    exampleScale
    genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq




theorem
    genBoundedCaseReplacedPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred :
    HasCriticalNu Ising3DModel
      blockRGFKComposedIsingCorrelationLength
      ((genBoundedCaseReplacedPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (genBoundedCaseReplacedPackage.retarget Ising3DModel)
    exampleScale
    genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem
    genBoundedCaseReplacedPackage_bridge_from_fkMassPowerTarget_congr_pred :
    ((genBoundedCaseReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      TFKM.isingCorrelationLength :=
  certificate_rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent
    (genBoundedCaseReplacedPackage.retarget Ising3DModel)
    exampleScale
    genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg
    TFKM



theorem
    genBoundedCaseReplacedPackage_valid_from_fkMassPowerTarget_congr_pred :
    ((genBoundedCaseReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).Valid TFKM.isingCorrelationLength :=
  certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent
    (genBoundedCaseReplacedPackage.retarget Ising3DModel)
    exampleScale
    genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg
    TFKM




theorem
    genBoundedCaseReplacedPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred :
    HasCriticalNu Ising3DModel TFKM.isingCorrelationLength
      ((genBoundedCaseReplacedPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent
    (genBoundedCaseReplacedPackage.retarget Ising3DModel)
    exampleScale
    genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg
    TFKM



theorem
    genCubicClassReplacedPackage_bridge_from_fk_pOfBeta_congr_pred :
    ((genCubicClassReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      blockRGFKComposedIsingCorrelationLength :=
  certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (genCubicClassReplacedPackage.retarget Ising3DModel)
    exampleScale
    genCubicClassReplacedPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem
    genCubicClassReplacedPackage_valid_from_fk_pOfBeta_congr_pred :
    ((genCubicClassReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).Valid
      blockRGFKComposedIsingCorrelationLength :=
  certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (genCubicClassReplacedPackage.retarget Ising3DModel)
    exampleScale
    genCubicClassReplacedPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq




theorem
    genCubicClassReplacedPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred :
    HasCriticalNu Ising3DModel
      blockRGFKComposedIsingCorrelationLength
      ((genCubicClassReplacedPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent
    (genCubicClassReplacedPackage.retarget Ising3DModel)
    exampleScale
    genCubicClassReplacedPackage_ising_predictedExponent_eq_rg
    blockRGFKToy_hasCriticalNu
    blockRGFKComposedIsingCorrelationLength_eventually_eq



theorem
    genCubicClassReplacedPackage_bridge_from_fkMassPowerTarget_congr_pred :
    ((genCubicClassReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      TFKM.isingCorrelationLength :=
  certificate_rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent
    (genCubicClassReplacedPackage.retarget Ising3DModel)
    exampleScale
    genCubicClassReplacedPackage_ising_predictedExponent_eq_rg
    TFKM



theorem
    genCubicClassReplacedPackage_valid_from_fkMassPowerTarget_congr_pred :
    ((genCubicClassReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).Valid TFKM.isingCorrelationLength :=
  certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent
    (genCubicClassReplacedPackage.retarget Ising3DModel)
    exampleScale
    genCubicClassReplacedPackage_ising_predictedExponent_eq_rg
    TFKM




theorem
    genCubicClassReplacedPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred :
    HasCriticalNu Ising3DModel TFKM.isingCorrelationLength
      ((genCubicClassReplacedPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent
    (genCubicClassReplacedPackage.retarget Ising3DModel)
    exampleScale
    genCubicClassReplacedPackage_ising_predictedExponent_eq_rg
    TFKM

end TableClosedBallExamples

end PackageFKBridgeExample
end Exact3D
end StatMech

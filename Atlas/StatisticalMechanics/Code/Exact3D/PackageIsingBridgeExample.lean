/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.IsingFinitePlusTailBridge
import Code.Exact3D.IsingTableClosedBallBridge
import Code.Exact3D.IsingWitnessBridge
import Code.Exact3D.PackageExponentMatchingExample










namespace StatMech
namespace Exact3D
namespace PackageIsingBridgeExample

open FinitePlusTailContractionExample
open FiniteWitnessPackageExample
open InfiniteTailWitnessPackageExample
open PackageExponentMatchingExample

variable
  (T :
    IsingAnalyticRGToExponentTarget
      (halfThirdScalingRGCertificate.retarget Ising3DModel))

variable
  (TM :
    IsingMassPowerLawAnalyticRGToExponentTarget
      (halfThirdScalingRGCertificate.retarget Ising3DModel))

variable
  (TC :
    IsingRGCoordinateBridgeInputs
      (halfThirdScalingRGCertificate.retarget Ising3DModel))

variable
  (TMC :
    IsingMassRGCoordinateBridgeInputs
      (halfThirdScalingRGCertificate.retarget Ising3DModel))

variable
  (TFM :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget
      (halfThirdScalingRGCertificate.retarget Ising3DModel))

section FiniteWitnessExamples

open FiniteWitnessPackage



theorem contributionSplitWitnessPackage_bridge_from_isingTarget_congr_pred :
    (contributionSplitWitnessPackage.retarget
      Ising3DModel).certificate.RGToExponentBridge T.correlationLength :=
  rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent
    (contributionSplitWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.contributionSplitWitnessPackage_ising_predictedExponent_eq_rg
    T



theorem contributionSplitWitnessPackage_valid_from_isingTarget_congr_pred :
    (contributionSplitWitnessPackage.retarget Ising3DModel).certificate.Valid
      T.correlationLength :=
  valid_of_isingAnalyticTarget_congr_predictedExponent
    (contributionSplitWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.contributionSplitWitnessPackage_ising_predictedExponent_eq_rg
    T



theorem contributionSplitWitnessPackage_hasCriticalNu_from_isingTarget_congr_pred :
    HasCriticalNu Ising3DModel T.correlationLength
      ((contributionSplitWitnessPackage.retarget
        Ising3DModel).certificate).predictedExponent :=
  hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent
    (contributionSplitWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.contributionSplitWitnessPackage_ising_predictedExponent_eq_rg
    T

end FiniteWitnessExamples

section InfiniteWitnessExamples

open InfiniteTailWitnessPackage



theorem geometricTailWitnessPackage_bridge_from_isingTarget_congr_pred :
    (geometricTailWitnessPackage.retarget
      Ising3DModel).certificate.RGToExponentBridge T.correlationLength :=
  rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent
    (geometricTailWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.geometricTailWitnessPackage_ising_predictedExponent_eq_rg
    T



theorem geometricTailWitnessPackage_valid_from_isingTarget_congr_pred :
    (geometricTailWitnessPackage.retarget Ising3DModel).certificate.Valid
      T.correlationLength :=
  valid_of_isingAnalyticTarget_congr_predictedExponent
    (geometricTailWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.geometricTailWitnessPackage_ising_predictedExponent_eq_rg
    T



theorem geometricTailWitnessPackage_hasCriticalNu_from_isingTarget_congr_pred :
    HasCriticalNu Ising3DModel T.correlationLength
      ((geometricTailWitnessPackage.retarget
        Ising3DModel).certificate).predictedExponent :=
  hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent
    (geometricTailWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.geometricTailWitnessPackage_ising_predictedExponent_eq_rg
    T

end InfiniteWitnessExamples

section TableWitnessExamples

open InfiniteTailTableWitnessPackage



theorem zeroStableKeyTableWitnessPackage_bridge_from_isingTarget_congr_pred :
    (zeroTableClosedBallRGPackage.tableWitness.retarget
      Ising3DModel).certificate.RGToExponentBridge T.correlationLength :=
  rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel)
    PackageExponentMatchingExample.zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg
    T



theorem zeroStableKeyTableWitnessPackage_valid_from_isingTarget_congr_pred :
    (zeroTableClosedBallRGPackage.tableWitness.retarget
      Ising3DModel).certificate.Valid T.correlationLength :=
  valid_of_isingAnalyticTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel)
    PackageExponentMatchingExample.zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg
    T



theorem zeroStableKeyTableWitnessPackage_hasCriticalNu_from_isingTarget_congr_pred :
    HasCriticalNu Ising3DModel T.correlationLength
      ((zeroTableClosedBallRGPackage.tableWitness.retarget
        Ising3DModel).certificate).predictedExponent :=
  hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel)
    PackageExponentMatchingExample.zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg
    T

end TableWitnessExamples

section HyperbolicExamples

open FinitePlusTailHyperbolicSplitting



theorem halfThirdScalingHyperbolic_bridge_from_isingTarget_congr_pred :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  certificate_rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg
    T



theorem halfThirdScalingHyperbolic_valid_from_isingTarget_congr_pred :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid T.correlationLength :=
  certificate_valid_of_isingAnalyticTarget_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg
    T



theorem halfThirdScalingHyperbolic_hasCriticalNu_from_isingTarget_congr_pred :
    HasCriticalNu Ising3DModel T.correlationLength
      (halfThirdScalingHyperbolicSplitting.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  certificate_hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg
    T

end HyperbolicExamples

section BlockRGExamples

open FinitePlusTailBlockRGPackage



theorem halfThirdScalingBlockRGPackage_bridge_from_isingTarget_congr_pred :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  certificate_rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingBlockRGPackage_ising_predictedExponent_eq_rg
    T



theorem halfThirdScalingBlockRGPackage_valid_from_isingTarget_congr_pred :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid T.correlationLength :=
  certificate_valid_of_isingAnalyticTarget_congr_predictedExponent
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingBlockRGPackage_ising_predictedExponent_eq_rg
    T



theorem halfThirdScalingBlockRGPackage_hasCriticalNu_from_isingTarget_congr_pred :
    HasCriticalNu Ising3DModel T.correlationLength
      (halfThirdScalingBlockRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  certificate_hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingBlockRGPackage_ising_predictedExponent_eq_rg
    T

end BlockRGExamples

section ClosedBallExamples

open FinitePlusTailClosedBallRGPackage



theorem halfThirdScalingClosedBall_bridge_from_isingTarget_congr_pred :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      T.correlationLength :=
  certificate_rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingClosedBall_ising_predictedExponent_eq_rg
    T



theorem halfThirdScalingClosedBall_valid_from_isingTarget_congr_pred :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid T.correlationLength :=
  certificate_valid_of_isingAnalyticTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingClosedBall_ising_predictedExponent_eq_rg
    T



theorem halfThirdScalingClosedBall_hasCriticalNu_from_isingTarget_congr_pred :
    HasCriticalNu Ising3DModel T.correlationLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  certificate_hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingClosedBall_ising_predictedExponent_eq_rg
    T

end ClosedBallExamples

section TableClosedBallExamples

open InfiniteTailTableClosedBallRGPackage



theorem zeroTableClosedBallRGPackage_bridge_from_isingTarget_congr_pred :
    ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
      exampleScale).RGToExponentBridge T.correlationLength :=
  certificate_rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    PackageExponentMatchingExample.zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    T



theorem zeroTableClosedBallRGPackage_valid_from_isingTarget_congr_pred :
    ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
      exampleScale).Valid T.correlationLength :=
  certificate_valid_of_isingAnalyticTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    PackageExponentMatchingExample.zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    T



theorem zeroTableClosedBallRGPackage_hasCriticalNu_from_isingTarget_congr_pred :
    HasCriticalNu Ising3DModel T.correlationLength
      ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
        exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    PackageExponentMatchingExample.zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    T



theorem generatedReplacedTCBRGPackage_bridge_from_isingTarget_congr_pred :
    ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      T.correlationLength :=
  certificate_rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent
    (generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    T



theorem
    generatedReplacedTCBRGPackage_valid_from_isingTarget_congr_pred :
    ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).Valid T.correlationLength :=
  certificate_valid_of_isingAnalyticTarget_congr_predictedExponent
    (generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    T




theorem
    generatedReplacedTCBRGPackage_hasCriticalNu_from_isingTarget_congr_pred :
    HasCriticalNu Ising3DModel T.correlationLength
      ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent
    (generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    T



theorem genMinCubicKeyReplacedPackage_bridge_from_isingTarget_congr_pred :
    ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      T.correlationLength :=
  certificate_rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent
    (genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg
    T



theorem genMinCubicKeyReplacedPackage_valid_from_isingTarget_congr_pred :
    ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).Valid T.correlationLength :=
  certificate_valid_of_isingAnalyticTarget_congr_predictedExponent
    (genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg
    T



theorem genMinCubicKeyReplacedPackage_hasCriticalNu_from_isingTarget_congr_pred :
    HasCriticalNu Ising3DModel T.correlationLength
      ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent
    (genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg
    T



theorem genBoundedCaseReplacedPackage_bridge_from_isingTarget_congr_pred :
    ((genBoundedCaseReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      T.correlationLength :=
  certificate_rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent
    (genBoundedCaseReplacedPackage.retarget Ising3DModel)
    exampleScale
    genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg
    T



theorem genBoundedCaseReplacedPackage_valid_from_isingTarget_congr_pred :
    ((genBoundedCaseReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).Valid T.correlationLength :=
  certificate_valid_of_isingAnalyticTarget_congr_predictedExponent
    (genBoundedCaseReplacedPackage.retarget Ising3DModel)
    exampleScale
    genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg
    T



theorem genBoundedCaseReplacedPackage_hasCriticalNu_from_isingTarget_congr_pred :
    HasCriticalNu Ising3DModel T.correlationLength
      ((genBoundedCaseReplacedPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent
    (genBoundedCaseReplacedPackage.retarget Ising3DModel)
    exampleScale
    genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg
    T



theorem genCubicClassReplacedPackage_bridge_from_isingTarget_congr_pred :
    ((genCubicClassReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      T.correlationLength :=
  certificate_rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent
    (genCubicClassReplacedPackage.retarget Ising3DModel)
    exampleScale
    genCubicClassReplacedPackage_ising_predictedExponent_eq_rg
    T



theorem genCubicClassReplacedPackage_valid_from_isingTarget_congr_pred :
    ((genCubicClassReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).Valid T.correlationLength :=
  certificate_valid_of_isingAnalyticTarget_congr_predictedExponent
    (genCubicClassReplacedPackage.retarget Ising3DModel)
    exampleScale
    genCubicClassReplacedPackage_ising_predictedExponent_eq_rg
    T



theorem genCubicClassReplacedPackage_hasCriticalNu_from_isingTarget_congr_pred :
    HasCriticalNu Ising3DModel T.correlationLength
      ((genCubicClassReplacedPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent
    (genCubicClassReplacedPackage.retarget Ising3DModel)
    exampleScale
    genCubicClassReplacedPackage_ising_predictedExponent_eq_rg
    T

end TableClosedBallExamples

section CoordinateBridgeExamples



theorem contributionSplitWitnessPackage_bridge_from_isingCoordinate_congr_pred :
    (contributionSplitWitnessPackage.retarget
      Ising3DModel).certificate.RGToExponentBridge
      TC.scaffold.correlationLength :=
  open FiniteWitnessPackage in
  rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (contributionSplitWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.contributionSplitWitnessPackage_ising_predictedExponent_eq_rg
    TC



theorem
    contributionSplitWitnessPackage_bridge_from_isingMassCoordinate_congr_pred :
    (contributionSplitWitnessPackage.retarget
      Ising3DModel).certificate.RGToExponentBridge
      TMC.scaffold.correlationLength :=
  open FiniteWitnessPackage in
  rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (contributionSplitWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.contributionSplitWitnessPackage_ising_predictedExponent_eq_rg
    TMC



theorem contributionSplitWitnessPackage_valid_from_isingCoordinate_congr_pred :
    (contributionSplitWitnessPackage.retarget Ising3DModel).certificate.Valid
      TC.scaffold.correlationLength :=
  open FiniteWitnessPackage in
  valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (contributionSplitWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.contributionSplitWitnessPackage_ising_predictedExponent_eq_rg
    TC



theorem
    contributionSplitWitnessPackage_hasCriticalNu_from_isingCoordinate_congr_pred :
    HasCriticalNu Ising3DModel TC.scaffold.correlationLength
      ((contributionSplitWitnessPackage.retarget
        Ising3DModel).certificate).predictedExponent :=
  open FiniteWitnessPackage in
  hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (contributionSplitWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.contributionSplitWitnessPackage_ising_predictedExponent_eq_rg
    TC



theorem
    contributionSplitWitnessPackage_valid_from_isingMassCoordinate_congr_pred :
    (contributionSplitWitnessPackage.retarget Ising3DModel).certificate.Valid
      TMC.scaffold.correlationLength :=
  open FiniteWitnessPackage in
  valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (contributionSplitWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.contributionSplitWitnessPackage_ising_predictedExponent_eq_rg
    TMC



theorem
    contributionSplitWitnessPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred :
    HasCriticalNu Ising3DModel TMC.scaffold.correlationLength
      ((contributionSplitWitnessPackage.retarget
        Ising3DModel).certificate).predictedExponent :=
  open FiniteWitnessPackage in
  hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (contributionSplitWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.contributionSplitWitnessPackage_ising_predictedExponent_eq_rg
    TMC



theorem geometricTailWitnessPackage_bridge_from_isingCoordinate_congr_pred :
    (geometricTailWitnessPackage.retarget
      Ising3DModel).certificate.RGToExponentBridge
      TC.scaffold.correlationLength :=
  open InfiniteTailWitnessPackage in
  rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (geometricTailWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.geometricTailWitnessPackage_ising_predictedExponent_eq_rg
    TC



theorem geometricTailWitnessPackage_valid_from_isingCoordinate_congr_pred :
    (geometricTailWitnessPackage.retarget Ising3DModel).certificate.Valid
      TC.scaffold.correlationLength :=
  open InfiniteTailWitnessPackage in
  valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (geometricTailWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.geometricTailWitnessPackage_ising_predictedExponent_eq_rg
    TC



theorem geometricTailWitnessPackage_hasCriticalNu_from_isingCoordinate_congr_pred :
    HasCriticalNu Ising3DModel TC.scaffold.correlationLength
      ((geometricTailWitnessPackage.retarget
        Ising3DModel).certificate).predictedExponent :=
  open InfiniteTailWitnessPackage in
  hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (geometricTailWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.geometricTailWitnessPackage_ising_predictedExponent_eq_rg
    TC



theorem
    geometricTailWitnessPackage_bridge_from_isingMassCoordinate_congr_pred :
    (geometricTailWitnessPackage.retarget
      Ising3DModel).certificate.RGToExponentBridge
      TMC.scaffold.correlationLength :=
  open InfiniteTailWitnessPackage in
  rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (geometricTailWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.geometricTailWitnessPackage_ising_predictedExponent_eq_rg
    TMC



theorem geometricTailWitnessPackage_valid_from_isingMassCoordinate_congr_pred :
    (geometricTailWitnessPackage.retarget Ising3DModel).certificate.Valid
      TMC.scaffold.correlationLength :=
  open InfiniteTailWitnessPackage in
  valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (geometricTailWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.geometricTailWitnessPackage_ising_predictedExponent_eq_rg
    TMC



theorem
    geometricTailWitnessPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred :
    HasCriticalNu Ising3DModel TMC.scaffold.correlationLength
      ((geometricTailWitnessPackage.retarget
        Ising3DModel).certificate).predictedExponent :=
  open InfiniteTailWitnessPackage in
  hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (geometricTailWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.geometricTailWitnessPackage_ising_predictedExponent_eq_rg
    TMC




theorem zeroStableKeyTableWitnessPackage_bridge_from_isingCoordinate_congr_pred :
    (zeroTableClosedBallRGPackage.tableWitness.retarget
      Ising3DModel).certificate.RGToExponentBridge
      TC.scaffold.correlationLength :=
  open InfiniteTailTableWitnessPackage in
  rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel)
    PackageExponentMatchingExample.zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg
    TC




theorem zeroStableKeyTableWitnessPackage_valid_from_isingCoordinate_congr_pred :
    (zeroTableClosedBallRGPackage.tableWitness.retarget
      Ising3DModel).certificate.Valid TC.scaffold.correlationLength :=
  open InfiniteTailTableWitnessPackage in
  valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel)
    PackageExponentMatchingExample.zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg
    TC



theorem
    zeroStableKeyTableWitnessPackage_hasCriticalNu_from_isingCoordinate_congr_pred :
    HasCriticalNu Ising3DModel TC.scaffold.correlationLength
      ((zeroTableClosedBallRGPackage.tableWitness.retarget
        Ising3DModel).certificate).predictedExponent :=
  open InfiniteTailTableWitnessPackage in
  hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel)
    PackageExponentMatchingExample.zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg
    TC




theorem
    zeroStableKeyTableWitnessPackage_bridge_from_isingMassCoordinate_congr_pred :
    (zeroTableClosedBallRGPackage.tableWitness.retarget
      Ising3DModel).certificate.RGToExponentBridge
      TMC.scaffold.correlationLength :=
  open InfiniteTailTableWitnessPackage in
  rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel)
    PackageExponentMatchingExample.zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg
    TMC




theorem
    zeroStableKeyTableWitnessPackage_valid_from_isingMassCoordinate_congr_pred :
    (zeroTableClosedBallRGPackage.tableWitness.retarget
      Ising3DModel).certificate.Valid TMC.scaffold.correlationLength :=
  open InfiniteTailTableWitnessPackage in
  valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel)
    PackageExponentMatchingExample.zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg
    TMC



theorem
    zeroStableKeyTableWitnessPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred :
    HasCriticalNu Ising3DModel TMC.scaffold.correlationLength
      ((zeroTableClosedBallRGPackage.tableWitness.retarget
        Ising3DModel).certificate).predictedExponent :=
  open InfiniteTailTableWitnessPackage in
  hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel)
    PackageExponentMatchingExample.zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg
    TMC



theorem halfThirdScalingHyperbolic_bridge_from_isingCoordinate_congr_pred :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      TC.scaffold.correlationLength :=
  open FinitePlusTailHyperbolicSplitting in
  certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg
    TC

theorem halfThirdScalingHyperbolic_valid_from_isingCoordinate_congr_pred :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid
      TC.scaffold.correlationLength :=
  open FinitePlusTailHyperbolicSplitting in
  certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg
    TC



theorem halfThirdScalingHyperbolic_hasCriticalNu_from_isingCoordinate_congr_pred :
    HasCriticalNu Ising3DModel TC.scaffold.correlationLength
      (halfThirdScalingHyperbolicSplitting.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  open FinitePlusTailHyperbolicSplitting in
  certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg
    TC



theorem
    halfThirdScalingHyperbolic_bridge_from_isingMassCoordinate_congr_pred :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      TMC.scaffold.correlationLength :=
  open FinitePlusTailHyperbolicSplitting in
  certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg
    TMC

theorem halfThirdScalingHyperbolic_valid_from_isingMassCoordinate_congr_pred :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid
      TMC.scaffold.correlationLength :=
  open FinitePlusTailHyperbolicSplitting in
  certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg
    TMC



theorem
    halfThirdScalingHyperbolic_hasCriticalNu_from_isingMassCoordinate_congr_pred :
    HasCriticalNu Ising3DModel TMC.scaffold.correlationLength
      (halfThirdScalingHyperbolicSplitting.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  open FinitePlusTailHyperbolicSplitting in
  certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg
    TMC



theorem halfThirdScalingBlockRGPackage_bridge_from_isingCoordinate_congr_pred :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      TC.scaffold.correlationLength :=
  open FinitePlusTailBlockRGPackage in
  certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingBlockRGPackage_ising_predictedExponent_eq_rg
    TC

theorem halfThirdScalingBlockRGPackage_valid_from_isingCoordinate_congr_pred :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid
      TC.scaffold.correlationLength :=
  open FinitePlusTailBlockRGPackage in
  certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingBlockRGPackage_ising_predictedExponent_eq_rg
    TC



theorem halfThirdScalingBlockRGPackage_hasCriticalNu_from_isingCoordinate_congr_pred :
    HasCriticalNu Ising3DModel TC.scaffold.correlationLength
      (halfThirdScalingBlockRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  open FinitePlusTailBlockRGPackage in
  certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingBlockRGPackage_ising_predictedExponent_eq_rg
    TC



theorem
    halfThirdScalingBlockRGPackage_bridge_from_isingMassCoordinate_congr_pred :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      TMC.scaffold.correlationLength :=
  open FinitePlusTailBlockRGPackage in
  certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingBlockRGPackage_ising_predictedExponent_eq_rg
    TMC

theorem halfThirdScalingBlockRGPackage_valid_from_isingMassCoordinate_congr_pred :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid
      TMC.scaffold.correlationLength :=
  open FinitePlusTailBlockRGPackage in
  certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingBlockRGPackage_ising_predictedExponent_eq_rg
    TMC



theorem
    halfThirdScalingBlockRGPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred :
    HasCriticalNu Ising3DModel TMC.scaffold.correlationLength
      (halfThirdScalingBlockRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  open FinitePlusTailBlockRGPackage in
  certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingBlockRGPackage_ising_predictedExponent_eq_rg
    TMC



theorem halfThirdScalingClosedBall_bridge_from_isingCoordinate_congr_pred :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      TC.scaffold.correlationLength :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingClosedBall_ising_predictedExponent_eq_rg
    TC

theorem halfThirdScalingClosedBall_valid_from_isingCoordinate_congr_pred :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid
      TC.scaffold.correlationLength :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingClosedBall_ising_predictedExponent_eq_rg
    TC



theorem halfThirdScalingClosedBall_hasCriticalNu_from_isingCoordinate_congr_pred :
    HasCriticalNu Ising3DModel TC.scaffold.correlationLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingClosedBall_ising_predictedExponent_eq_rg
    TC



theorem halfThirdScalingClosedBall_bridge_from_isingMassCoordinate_congr_pred :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      TMC.scaffold.correlationLength :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingClosedBall_ising_predictedExponent_eq_rg
    TMC

theorem halfThirdScalingClosedBall_valid_from_isingMassCoordinate_congr_pred :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid
      TMC.scaffold.correlationLength :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingClosedBall_ising_predictedExponent_eq_rg
    TMC



theorem halfThirdScalingClosedBall_hasCriticalNu_from_isingMassCoordinate_congr_pred :
    HasCriticalNu Ising3DModel TMC.scaffold.correlationLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingClosedBall_ising_predictedExponent_eq_rg
    TMC



theorem zeroTableClosedBallRGPackage_bridge_from_isingCoordinate_congr_pred :
    ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
      exampleScale).RGToExponentBridge TC.scaffold.correlationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    PackageExponentMatchingExample.zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TC

theorem zeroTableClosedBallRGPackage_valid_from_isingCoordinate_congr_pred :
    ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
      exampleScale).Valid TC.scaffold.correlationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    PackageExponentMatchingExample.zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TC



theorem zeroTableClosedBallRGPackage_hasCriticalNu_from_isingCoordinate_congr_pred :
    HasCriticalNu Ising3DModel TC.scaffold.correlationLength
      ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
        exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    PackageExponentMatchingExample.zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TC



theorem
    zeroTableClosedBallRGPackage_bridge_from_isingMassCoordinate_congr_pred :
    ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
      exampleScale).RGToExponentBridge TMC.scaffold.correlationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    PackageExponentMatchingExample.zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TMC

theorem zeroTableClosedBallRGPackage_valid_from_isingMassCoordinate_congr_pred :
    ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
      exampleScale).Valid TMC.scaffold.correlationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    PackageExponentMatchingExample.zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TMC



theorem
    zeroTableClosedBallRGPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred :
    HasCriticalNu Ising3DModel TMC.scaffold.correlationLength
      ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
        exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    PackageExponentMatchingExample.zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TMC




theorem generatedReplacedTCBRGPackage_bridge_from_isingCoordinate_congr_pred :
    ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      TC.scaffold.correlationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TC

theorem generatedReplacedTCBRGPackage_valid_from_isingCoordinate_congr_pred :
    ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).Valid
      TC.scaffold.correlationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TC




theorem generatedReplacedTCBRGPackage_hasCriticalNu_from_isingCoordinate_congr_pred :
    HasCriticalNu Ising3DModel TC.scaffold.correlationLength
      ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TC




theorem
    generatedReplacedTCBRGPackage_bridge_from_isingMassCoordinate_congr_pred :
    ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      TMC.scaffold.correlationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TMC

theorem generatedReplacedTCBRGPackage_valid_from_isingMassCoordinate_congr_pred :
    ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).Valid
      TMC.scaffold.correlationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TMC




theorem generatedReplacedTCBRGPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred :
    HasCriticalNu Ising3DModel TMC.scaffold.correlationLength
      ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TMC




theorem genMinCubicKeyReplacedPackage_bridge_from_isingCoordinate_congr_pred :
    ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      TC.scaffold.correlationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg
    TC

theorem genMinCubicKeyReplacedPackage_valid_from_isingCoordinate_congr_pred :
    ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).Valid
      TC.scaffold.correlationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg
    TC




theorem
    genMinCubicKeyReplacedPackage_hasCriticalNu_from_isingCoordinate_congr_pred :
    HasCriticalNu Ising3DModel TC.scaffold.correlationLength
      ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg
    TC




theorem
    genMinCubicKeyReplacedPackage_bridge_from_isingMassCoordinate_congr_pred :
    ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      TMC.scaffold.correlationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg
    TMC

theorem genMinCubicKeyReplacedPackage_valid_from_isingMassCoordinate_congr_pred :
    ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).Valid
      TMC.scaffold.correlationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg
    TMC




theorem
    genMinCubicKeyReplacedPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred :
    HasCriticalNu Ising3DModel TMC.scaffold.correlationLength
      ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg
    TMC




theorem genBoundedCaseReplacedPackage_bridge_from_isingCoordinate_congr_pred :
    ((genBoundedCaseReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      TC.scaffold.correlationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (genBoundedCaseReplacedPackage.retarget Ising3DModel)
    exampleScale
    genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg
    TC

theorem genBoundedCaseReplacedPackage_valid_from_isingCoordinate_congr_pred :
    ((genBoundedCaseReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).Valid
      TC.scaffold.correlationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (genBoundedCaseReplacedPackage.retarget Ising3DModel)
    exampleScale
    genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg
    TC




theorem
    genBoundedCaseReplacedPackage_hasCriticalNu_from_isingCoordinate_congr_pred :
    HasCriticalNu Ising3DModel TC.scaffold.correlationLength
      ((genBoundedCaseReplacedPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (genBoundedCaseReplacedPackage.retarget Ising3DModel)
    exampleScale
    genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg
    TC




theorem
    genBoundedCaseReplacedPackage_bridge_from_isingMassCoordinate_congr_pred :
    ((genBoundedCaseReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      TMC.scaffold.correlationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (genBoundedCaseReplacedPackage.retarget Ising3DModel)
    exampleScale
    genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg
    TMC

theorem genBoundedCaseReplacedPackage_valid_from_isingMassCoordinate_congr_pred :
    ((genBoundedCaseReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).Valid
      TMC.scaffold.correlationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (genBoundedCaseReplacedPackage.retarget Ising3DModel)
    exampleScale
    genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg
    TMC




theorem
    genBoundedCaseReplacedPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred :
    HasCriticalNu Ising3DModel TMC.scaffold.correlationLength
      ((genBoundedCaseReplacedPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (genBoundedCaseReplacedPackage.retarget Ising3DModel)
    exampleScale
    genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg
    TMC




theorem genCubicClassReplacedPackage_bridge_from_isingCoordinate_congr_pred :
    ((genCubicClassReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      TC.scaffold.correlationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (genCubicClassReplacedPackage.retarget Ising3DModel)
    exampleScale
    genCubicClassReplacedPackage_ising_predictedExponent_eq_rg
    TC

theorem genCubicClassReplacedPackage_valid_from_isingCoordinate_congr_pred :
    ((genCubicClassReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).Valid
      TC.scaffold.correlationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (genCubicClassReplacedPackage.retarget Ising3DModel)
    exampleScale
    genCubicClassReplacedPackage_ising_predictedExponent_eq_rg
    TC




theorem
    genCubicClassReplacedPackage_hasCriticalNu_from_isingCoordinate_congr_pred :
    HasCriticalNu Ising3DModel TC.scaffold.correlationLength
      ((genCubicClassReplacedPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent
    (genCubicClassReplacedPackage.retarget Ising3DModel)
    exampleScale
    genCubicClassReplacedPackage_ising_predictedExponent_eq_rg
    TC




theorem
    genCubicClassReplacedPackage_bridge_from_isingMassCoordinate_congr_pred :
    ((genCubicClassReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      TMC.scaffold.correlationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (genCubicClassReplacedPackage.retarget Ising3DModel)
    exampleScale
    genCubicClassReplacedPackage_ising_predictedExponent_eq_rg
    TMC

theorem genCubicClassReplacedPackage_valid_from_isingMassCoordinate_congr_pred :
    ((genCubicClassReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).Valid
      TMC.scaffold.correlationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (genCubicClassReplacedPackage.retarget Ising3DModel)
    exampleScale
    genCubicClassReplacedPackage_ising_predictedExponent_eq_rg
    TMC




theorem
    genCubicClassReplacedPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred :
    HasCriticalNu Ising3DModel TMC.scaffold.correlationLength
      ((genCubicClassReplacedPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent
    (genCubicClassReplacedPackage.retarget Ising3DModel)
    exampleScale
    genCubicClassReplacedPackage_ising_predictedExponent_eq_rg
    TMC

end CoordinateBridgeExamples

section MassPowerWitnessExamples



theorem contributionSplitWitnessPackage_bridge_from_isingMassPowerTarget_congr_pred :
    (contributionSplitWitnessPackage.retarget
      Ising3DModel).certificate.RGToExponentBridge TM.correlationLength :=
  open FiniteWitnessPackage in
  rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent
    (contributionSplitWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.contributionSplitWitnessPackage_ising_predictedExponent_eq_rg
    TM



theorem contributionSplitWitnessPackage_bridge_from_isingMassPower_congr_pred :
    (contributionSplitWitnessPackage.retarget
      Ising3DModel).certificate.RGToExponentBridge TM.correlationLength :=
  contributionSplitWitnessPackage_bridge_from_isingMassPowerTarget_congr_pred
    TM



theorem
    contributionSplitWitnessPackage_bridge_from_freeMassPowerToPlus_congr_pred :
    (contributionSplitWitnessPackage.retarget
      Ising3DModel).certificate.RGToExponentBridge TFM.correlationLength :=
  open FiniteWitnessPackage in
  rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (contributionSplitWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.contributionSplitWitnessPackage_ising_predictedExponent_eq_rg
    TFM



theorem contributionSplitWitnessPackage_valid_from_isingMassPower_congr_pred :
    (contributionSplitWitnessPackage.retarget Ising3DModel).certificate.Valid
      TM.correlationLength :=
  open FiniteWitnessPackage in
  valid_of_isingMassPowerLawTarget_congr_predictedExponent
    (contributionSplitWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.contributionSplitWitnessPackage_ising_predictedExponent_eq_rg
    TM



theorem contributionSplitWitnessPackage_hasCriticalNu_from_isingMassPower_congr_pred :
    HasCriticalNu Ising3DModel TM.correlationLength
      ((contributionSplitWitnessPackage.retarget
        Ising3DModel).certificate).predictedExponent :=
  open FiniteWitnessPackage in
  hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent
    (contributionSplitWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.contributionSplitWitnessPackage_ising_predictedExponent_eq_rg
    TM



theorem
    contributionSplitWitnessPackage_valid_from_freeMassPowerToPlus_congr_pred :
    (contributionSplitWitnessPackage.retarget Ising3DModel).certificate.Valid
      TFM.correlationLength :=
  open FiniteWitnessPackage in
  valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (contributionSplitWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.contributionSplitWitnessPackage_ising_predictedExponent_eq_rg
    TFM



theorem
    contributionSplitWitnessPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred :
    HasCriticalNu Ising3DModel TFM.correlationLength
      ((contributionSplitWitnessPackage.retarget
        Ising3DModel).certificate).predictedExponent :=
  open FiniteWitnessPackage in
  hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (contributionSplitWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.contributionSplitWitnessPackage_ising_predictedExponent_eq_rg
    TFM



theorem geometricTailWitnessPackage_bridge_from_isingMassPower_congr_pred :
    (geometricTailWitnessPackage.retarget
      Ising3DModel).certificate.RGToExponentBridge TM.correlationLength :=
  open InfiniteTailWitnessPackage in
  rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent
    (geometricTailWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.geometricTailWitnessPackage_ising_predictedExponent_eq_rg
    TM



theorem geometricTailWitnessPackage_valid_from_isingMassPower_congr_pred :
    (geometricTailWitnessPackage.retarget Ising3DModel).certificate.Valid
      TM.correlationLength :=
  open InfiniteTailWitnessPackage in
  valid_of_isingMassPowerLawTarget_congr_predictedExponent
    (geometricTailWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.geometricTailWitnessPackage_ising_predictedExponent_eq_rg
    TM



theorem geometricTailWitnessPackage_hasCriticalNu_from_isingMassPower_congr_pred :
    HasCriticalNu Ising3DModel TM.correlationLength
      ((geometricTailWitnessPackage.retarget
        Ising3DModel).certificate).predictedExponent :=
  open InfiniteTailWitnessPackage in
  hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent
    (geometricTailWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.geometricTailWitnessPackage_ising_predictedExponent_eq_rg
    TM



theorem geometricTailWitnessPackage_bridge_from_freeMassPowerToPlus_congr_pred :
    (geometricTailWitnessPackage.retarget
      Ising3DModel).certificate.RGToExponentBridge TFM.correlationLength :=
  open InfiniteTailWitnessPackage in
  rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (geometricTailWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.geometricTailWitnessPackage_ising_predictedExponent_eq_rg
    TFM



theorem geometricTailWitnessPackage_valid_from_freeMassPowerToPlus_congr_pred :
    (geometricTailWitnessPackage.retarget Ising3DModel).certificate.Valid
      TFM.correlationLength :=
  open InfiniteTailWitnessPackage in
  valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (geometricTailWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.geometricTailWitnessPackage_ising_predictedExponent_eq_rg
    TFM



theorem
    geometricTailWitnessPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred :
    HasCriticalNu Ising3DModel TFM.correlationLength
      ((geometricTailWitnessPackage.retarget
        Ising3DModel).certificate).predictedExponent :=
  open InfiniteTailWitnessPackage in
  hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (geometricTailWitnessPackage.retarget Ising3DModel)
    PackageExponentMatchingExample.geometricTailWitnessPackage_ising_predictedExponent_eq_rg
    TFM



theorem zeroStableKeyTableWitnessPackage_bridge_from_isingMassPower_congr_pred :
    (zeroTableClosedBallRGPackage.tableWitness.retarget
      Ising3DModel).certificate.RGToExponentBridge TM.correlationLength :=
  open InfiniteTailTableWitnessPackage in
  rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel)
    PackageExponentMatchingExample.zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg
    TM



theorem zeroStableKeyTableWitnessPackage_valid_from_isingMassPower_congr_pred :
    (zeroTableClosedBallRGPackage.tableWitness.retarget
      Ising3DModel).certificate.Valid TM.correlationLength :=
  open InfiniteTailTableWitnessPackage in
  valid_of_isingMassPowerLawTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel)
    PackageExponentMatchingExample.zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg
    TM



theorem zeroStableKeyTableWitnessPackage_hasCriticalNu_from_isingMassPower_congr_pred :
    HasCriticalNu Ising3DModel TM.correlationLength
      ((zeroTableClosedBallRGPackage.tableWitness.retarget
        Ising3DModel).certificate).predictedExponent :=
  open InfiniteTailTableWitnessPackage in
  hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel)
    PackageExponentMatchingExample.zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg
    TM



theorem
    zeroStableKeyTableWitnessPackage_bridge_from_freeMassPowerToPlus_congr_pred :
    (zeroTableClosedBallRGPackage.tableWitness.retarget
      Ising3DModel).certificate.RGToExponentBridge TFM.correlationLength :=
  open InfiniteTailTableWitnessPackage in
  rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel)
    PackageExponentMatchingExample.zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg
    TFM



theorem
    zeroStableKeyTableWitnessPackage_valid_from_freeMassPowerToPlus_congr_pred :
    (zeroTableClosedBallRGPackage.tableWitness.retarget
      Ising3DModel).certificate.Valid TFM.correlationLength :=
  open InfiniteTailTableWitnessPackage in
  valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel)
    PackageExponentMatchingExample.zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg
    TFM



theorem
    zeroStableKeyTableWitnessPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred :
    HasCriticalNu Ising3DModel TFM.correlationLength
      ((zeroTableClosedBallRGPackage.tableWitness.retarget
        Ising3DModel).certificate).predictedExponent :=
  open InfiniteTailTableWitnessPackage in
  hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel)
    PackageExponentMatchingExample.zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg
    TFM

end MassPowerWitnessExamples

section MassPowerFinitePlusTailExamples



theorem halfThirdScalingHyperbolic_bridge_from_isingMassTarget_congr_pred :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      TM.correlationLength :=
  open FinitePlusTailHyperbolicSplitting in
  certificate_rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg
    TM.toMassTarget



theorem halfThirdScalingHyperbolic_valid_from_isingMassTarget_congr_pred :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid TM.correlationLength :=
  open FinitePlusTailHyperbolicSplitting in
  certificate_valid_of_isingMassAnalyticTarget_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg
    TM.toMassTarget



theorem halfThirdScalingHyperbolic_hasCriticalNu_from_isingMassTarget_congr_pred :
    HasCriticalNu Ising3DModel TM.correlationLength
      (halfThirdScalingHyperbolicSplitting.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  open FinitePlusTailHyperbolicSplitting in
  certificate_hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg
    TM.toMassTarget



theorem
    halfThirdScalingHyperbolic_bridge_from_freeMassPowerToPlus_congr_pred :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      TFM.correlationLength :=
  open FinitePlusTailHyperbolicSplitting in
  certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg
    TFM



theorem halfThirdScalingHyperbolic_bridge_from_isingMassPower_congr_pred :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      TM.correlationLength :=
  open FinitePlusTailHyperbolicSplitting in
  certificate_rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg
    TM



theorem halfThirdScalingHyperbolic_valid_from_isingMassPower_congr_pred :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid TM.correlationLength :=
  open FinitePlusTailHyperbolicSplitting in
  certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg
    TM



theorem halfThirdScalingHyperbolic_hasCriticalNu_from_isingMassPower_congr_pred :
    HasCriticalNu Ising3DModel TM.correlationLength
      (halfThirdScalingHyperbolicSplitting.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  open FinitePlusTailHyperbolicSplitting in
  certificate_hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg
    TM



theorem halfThirdScalingHyperbolic_valid_from_freeMassPowerToPlus_congr_pred :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid TFM.correlationLength :=
  open FinitePlusTailHyperbolicSplitting in
  certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg
    TFM



theorem
    halfThirdScalingHyperbolic_hasCriticalNu_from_freeMassPowerToPlus_congr_pred :
    HasCriticalNu Ising3DModel TFM.correlationLength
      (halfThirdScalingHyperbolicSplitting.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  open FinitePlusTailHyperbolicSplitting in
  certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg
    TFM



theorem halfThirdScalingBlockRGPackage_bridge_from_isingMassPower_congr_pred :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      TM.correlationLength :=
  open FinitePlusTailBlockRGPackage in
  certificate_rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingBlockRGPackage_ising_predictedExponent_eq_rg
    TM



theorem halfThirdScalingBlockRGPackage_valid_from_isingMassPower_congr_pred :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid TM.correlationLength :=
  open FinitePlusTailBlockRGPackage in
  certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingBlockRGPackage_ising_predictedExponent_eq_rg
    TM



theorem halfThirdScalingBlockRGPackage_hasCriticalNu_from_isingMassPower_congr_pred :
    HasCriticalNu Ising3DModel TM.correlationLength
      (halfThirdScalingBlockRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  open FinitePlusTailBlockRGPackage in
  certificate_hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingBlockRGPackage_ising_predictedExponent_eq_rg
    TM



theorem
    halfThirdScalingBlockRGPackage_bridge_from_freeMassPowerToPlus_congr_pred :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      TFM.correlationLength :=
  open FinitePlusTailBlockRGPackage in
  certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingBlockRGPackage_ising_predictedExponent_eq_rg
    TFM



theorem halfThirdScalingBlockRGPackage_valid_from_freeMassPowerToPlus_congr_pred :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid TFM.correlationLength :=
  open FinitePlusTailBlockRGPackage in
  certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingBlockRGPackage_ising_predictedExponent_eq_rg
    TFM



theorem
    halfThirdScalingBlockRGPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred :
    HasCriticalNu Ising3DModel TFM.correlationLength
      (halfThirdScalingBlockRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  open FinitePlusTailBlockRGPackage in
  certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingBlockRGPackage_ising_predictedExponent_eq_rg
    TFM



theorem halfThirdScalingClosedBall_bridge_from_isingMassTarget_congr_pred :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      TM.correlationLength :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingClosedBall_ising_predictedExponent_eq_rg
    TM.toMassTarget



theorem halfThirdScalingClosedBall_valid_from_isingMassTarget_congr_pred :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid TM.correlationLength :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_valid_of_isingMassAnalyticTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingClosedBall_ising_predictedExponent_eq_rg
    TM.toMassTarget



theorem halfThirdScalingClosedBall_hasCriticalNu_from_isingMassTarget_congr_pred :
    HasCriticalNu Ising3DModel TM.correlationLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingClosedBall_ising_predictedExponent_eq_rg
    TM.toMassTarget



theorem halfThirdScalingClosedBall_bridge_from_isingMassPower_congr_pred :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      TM.correlationLength :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingClosedBall_ising_predictedExponent_eq_rg
    TM



theorem halfThirdScalingClosedBall_bridge_from_freeMassPowerToPlus_congr_pred :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge
      TFM.correlationLength :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingClosedBall_ising_predictedExponent_eq_rg
    TFM



theorem halfThirdScalingClosedBall_valid_from_isingMassPower_congr_pred :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid TM.correlationLength :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingClosedBall_ising_predictedExponent_eq_rg
    TM



theorem halfThirdScalingClosedBall_hasCriticalNu_from_isingMassPower_congr_pred :
    HasCriticalNu Ising3DModel TM.correlationLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingClosedBall_ising_predictedExponent_eq_rg
    TM



theorem halfThirdScalingClosedBall_valid_from_freeMassPowerToPlus_congr_pred :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).Valid TFM.correlationLength :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingClosedBall_ising_predictedExponent_eq_rg
    TFM



theorem
    halfThirdScalingClosedBall_hasCriticalNu_from_freeMassPowerToPlus_congr_pred :
    HasCriticalNu Ising3DModel TFM.correlationLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale Ising3DModel).predictedExponent :=
  open FinitePlusTailClosedBallRGPackage in
  certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    PackageExponentMatchingExample.halfThirdScalingClosedBall_ising_predictedExponent_eq_rg
    TFM

end MassPowerFinitePlusTailExamples

section MassPowerTableClosedBallExamples

open InfiniteTailTableClosedBallRGPackage



theorem zeroTableClosedBallRGPackage_bridge_from_isingMassPower_congr_pred :
    ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
      exampleScale).RGToExponentBridge TM.correlationLength :=
  certificate_rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    PackageExponentMatchingExample.zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TM



theorem zeroTableClosedBallRGPackage_valid_from_isingMassPower_congr_pred :
    ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
      exampleScale).Valid TM.correlationLength :=
  certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    PackageExponentMatchingExample.zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TM



theorem zeroTableClosedBallRGPackage_hasCriticalNu_from_isingMassPower_congr_pred :
    HasCriticalNu Ising3DModel TM.correlationLength
      ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
        exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    PackageExponentMatchingExample.zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TM




theorem
    generatedReplacedTCBRGPackage_bridge_from_isingMassPower_congr_pred :
    ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      TM.correlationLength :=
  certificate_rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent
    (generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TM



theorem
    generatedReplacedTCBRGPackage_valid_from_isingMassPower_congr_pred :
    ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).Valid TM.correlationLength :=
  certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent
    (generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TM




theorem
    generatedReplacedTCBRGPackage_hasCriticalNu_from_isingMassPower_congr_pred :
    HasCriticalNu Ising3DModel TM.correlationLength
      ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent
    (generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TM




theorem
    generatedReplacedTCBRGPackage_bridge_from_freeMassPowerToPlus_congr_pred :
    ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      TFM.correlationLength :=
  certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TFM



theorem
    zeroTableClosedBallRGPackage_bridge_from_freeMassPowerToPlus_congr_pred :
    ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
      exampleScale).RGToExponentBridge TFM.correlationLength :=
  certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    PackageExponentMatchingExample.zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TFM



theorem
    zeroTableClosedBallRGPackage_valid_from_freeMassPowerToPlus_congr_pred :
    ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
      exampleScale).Valid TFM.correlationLength :=
  certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    PackageExponentMatchingExample.zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TFM



theorem
    zeroTableClosedBallRGPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred :
    HasCriticalNu Ising3DModel TFM.correlationLength
      ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
        exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (zeroTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    PackageExponentMatchingExample.zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TFM



theorem generatedReplacedTCBRGPackage_valid_from_freeMassPowerToPlus_congr_pred :
    ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).Valid TFM.correlationLength :=
  certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TFM




theorem
    generatedReplacedTCBRGPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred :
    HasCriticalNu Ising3DModel TFM.correlationLength
      ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg
    TFM




theorem
    genMinCubicKeyReplacedPackage_bridge_from_isingMassPower_congr_pred :
    ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      TM.correlationLength :=
  certificate_rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent
    (genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg
    TM




theorem genMinCubicKeyReplacedPackage_valid_from_isingMassPower_congr_pred :
    ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).Valid TM.correlationLength :=
  certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent
    (genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg
    TM




theorem
    genMinCubicKeyReplacedPackage_hasCriticalNu_from_isingMassPower_congr_pred :
    HasCriticalNu Ising3DModel TM.correlationLength
      ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent
    (genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg
    TM




theorem
    genMinCubicKeyReplacedPackage_bridge_from_freeMassPowerToPlus_congr_pred :
    ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      TFM.correlationLength :=
  certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg
    TFM




theorem genMinCubicKeyReplacedPackage_valid_from_freeMassPowerToPlus_congr_pred :
    ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).Valid TFM.correlationLength :=
  certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg
    TFM




theorem
    genMinCubicKeyReplacedPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred :
    HasCriticalNu Ising3DModel TFM.correlationLength
      ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel)
    exampleScale
    genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg
    TFM




theorem
    genBoundedCaseReplacedPackage_bridge_from_isingMassPower_congr_pred :
    ((genBoundedCaseReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      TM.correlationLength :=
  certificate_rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent
    (genBoundedCaseReplacedPackage.retarget Ising3DModel)
    exampleScale
    genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg
    TM




theorem genBoundedCaseReplacedPackage_valid_from_isingMassPower_congr_pred :
    ((genBoundedCaseReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).Valid TM.correlationLength :=
  certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent
    (genBoundedCaseReplacedPackage.retarget Ising3DModel)
    exampleScale
    genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg
    TM




theorem
    genBoundedCaseReplacedPackage_hasCriticalNu_from_isingMassPower_congr_pred :
    HasCriticalNu Ising3DModel TM.correlationLength
      ((genBoundedCaseReplacedPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent
    (genBoundedCaseReplacedPackage.retarget Ising3DModel)
    exampleScale
    genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg
    TM




theorem
    genBoundedCaseReplacedPackage_bridge_from_freeMassPowerToPlus_congr_pred :
    ((genBoundedCaseReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      TFM.correlationLength :=
  certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (genBoundedCaseReplacedPackage.retarget Ising3DModel)
    exampleScale
    genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg
    TFM




theorem genBoundedCaseReplacedPackage_valid_from_freeMassPowerToPlus_congr_pred :
    ((genBoundedCaseReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).Valid TFM.correlationLength :=
  certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (genBoundedCaseReplacedPackage.retarget Ising3DModel)
    exampleScale
    genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg
    TFM




theorem
    genBoundedCaseReplacedPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred :
    HasCriticalNu Ising3DModel TFM.correlationLength
      ((genBoundedCaseReplacedPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (genBoundedCaseReplacedPackage.retarget Ising3DModel)
    exampleScale
    genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg
    TFM




theorem
    genCubicClassReplacedPackage_bridge_from_isingMassPower_congr_pred :
    ((genCubicClassReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      TM.correlationLength :=
  certificate_rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent
    (genCubicClassReplacedPackage.retarget Ising3DModel)
    exampleScale
    genCubicClassReplacedPackage_ising_predictedExponent_eq_rg
    TM



theorem genCubicClassReplacedPackage_valid_from_isingMassPower_congr_pred :
    ((genCubicClassReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).Valid TM.correlationLength :=
  certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent
    (genCubicClassReplacedPackage.retarget Ising3DModel)
    exampleScale
    genCubicClassReplacedPackage_ising_predictedExponent_eq_rg
    TM




theorem
    genCubicClassReplacedPackage_hasCriticalNu_from_isingMassPower_congr_pred :
    HasCriticalNu Ising3DModel TM.correlationLength
      ((genCubicClassReplacedPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent
    (genCubicClassReplacedPackage.retarget Ising3DModel)
    exampleScale
    genCubicClassReplacedPackage_ising_predictedExponent_eq_rg
    TM




theorem
    genCubicClassReplacedPackage_bridge_from_freeMassPowerToPlus_congr_pred :
    ((genCubicClassReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).RGToExponentBridge
      TFM.correlationLength :=
  certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (genCubicClassReplacedPackage.retarget Ising3DModel)
    exampleScale
    genCubicClassReplacedPackage_ising_predictedExponent_eq_rg
    TFM



theorem genCubicClassReplacedPackage_valid_from_freeMassPowerToPlus_congr_pred :
    ((genCubicClassReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).Valid TFM.correlationLength :=
  certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (genCubicClassReplacedPackage.retarget Ising3DModel)
    exampleScale
    genCubicClassReplacedPackage_ising_predictedExponent_eq_rg
    TFM




theorem
    genCubicClassReplacedPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred :
    HasCriticalNu Ising3DModel TFM.correlationLength
      ((genCubicClassReplacedPackage.retarget
        Ising3DModel).certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent
    (genCubicClassReplacedPackage.retarget Ising3DModel)
    exampleScale
    genCubicClassReplacedPackage_ising_predictedExponent_eq_rg
    TFM

end MassPowerTableClosedBallExamples

end PackageIsingBridgeExample
end Exact3D
end StatMech

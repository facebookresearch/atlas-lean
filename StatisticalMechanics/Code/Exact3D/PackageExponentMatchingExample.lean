/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.FinitePlusTailContractionExample
import Code.Exact3D.FiniteWitnessPackageExample
import Code.Exact3D.InfiniteTailWitnessPackageExample
import Code.Exact3D.Ising3D









namespace StatMech
namespace Exact3D
namespace PackageExponentMatchingExample

open FinitePlusTailContractionExample
open FiniteWitnessPackageExample
open InfiniteTailWitnessPackageExample



theorem halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale Ising3DModel).predictedExponent =
      (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent := by
  rw [RGCertificate.retarget_predictedExponent]
  rfl



theorem halfThirdScalingBlockRGPackage_ising_predictedExponent_eq_rg :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).predictedExponent =
      (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent := by
  rw [halfThirdScalingBlockRGPackage.certificate_predictedExponent_eq]
  rw [RGCertificate.retarget_predictedExponent]
  exact halfThirdScalingRGCertificate_predictedExponent_eq.symm



theorem halfThirdScalingClosedBall_ising_predictedExponent_eq_rg :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale Ising3DModel).predictedExponent =
      (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent := by
  rw [halfThirdScalingUnitClosedBallRGPackage.certificate_predictedExponent_eq]
  rw [RGCertificate.retarget_predictedExponent]
  exact halfThirdScalingRGCertificate_predictedExponent_eq.symm



theorem zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg :
    ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate
      exampleScale).predictedExponent =
      (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent := by
  rw [InfiniteTailTableClosedBallRGPackage.retarget_predictedExponent]
  rw [zeroTableClosedBallRGPackage_predictedExponent_eq]
  rw [RGCertificate.retarget_predictedExponent]
  rw [halfThirdScalingRGCertificate_predictedExponent_eq]
  simp [predictedNu, BlockScale.toReal, exampleScale, halfThirdScalingBlockScale]




theorem
    generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg :
    ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).predictedExponent =
      (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent := by
  rw [InfiniteTailTableClosedBallRGPackage.retarget_predictedExponent]
  rw [generatedStableKeyReplacedTableClosedBallRGPackage_predictedExponent_eq]
  rw [RGCertificate.retarget_predictedExponent]
  rw [halfThirdScalingRGCertificate_predictedExponent_eq]
  simp [predictedNu, BlockScale.toReal, exampleScale, halfThirdScalingBlockScale]




theorem genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg :
    ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget
      Ising3DModel).certificate exampleScale).predictedExponent =
      (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent := by
  rw [InfiniteTailTableClosedBallRGPackage.retarget_predictedExponent]
  rw [genMinCubicKeyReplacedTableClosedBallRGPackage_predictedExponent_eq]
  rw [RGCertificate.retarget_predictedExponent]
  rw [halfThirdScalingRGCertificate_predictedExponent_eq]
  simp [predictedNu, BlockScale.toReal, exampleScale, halfThirdScalingBlockScale]




theorem genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg :
    ((genBoundedCaseReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).predictedExponent =
      (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent := by
  rw [InfiniteTailTableClosedBallRGPackage.retarget_predictedExponent]
  rw [genBoundedCaseReplacedPackage_predictedExponent_eq]
  rw [RGCertificate.retarget_predictedExponent]
  rw [halfThirdScalingRGCertificate_predictedExponent_eq]
  simp [predictedNu, BlockScale.toReal, exampleScale, halfThirdScalingBlockScale]




theorem genCubicClassReplacedPackage_ising_predictedExponent_eq_rg :
    ((genCubicClassReplacedPackage.retarget
      Ising3DModel).certificate exampleScale).predictedExponent =
      (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent := by
  rw [InfiniteTailTableClosedBallRGPackage.retarget_predictedExponent]
  rw [genCubicClassReplacedPackage_predictedExponent_eq]
  rw [RGCertificate.retarget_predictedExponent]
  rw [halfThirdScalingRGCertificate_predictedExponent_eq]
  simp [predictedNu, BlockScale.toReal, exampleScale, halfThirdScalingBlockScale]



theorem contributionSplitWitnessPackage_ising_predictedExponent_eq_rg :
    ((contributionSplitWitnessPackage.retarget
      Ising3DModel).certificate).predictedExponent =
      (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent := by
  rw [FiniteWitnessPackage.retarget_predictedExponent]
  rw [contributionSplitWitnessPackage_predictedExponent_eq]
  rw [RGCertificate.retarget_predictedExponent]
  rw [halfThirdScalingRGCertificate_predictedExponent_eq]
  simp [predictedNu, BlockScale.toReal, exampleScale,
    halfThirdScalingBlockScale]



theorem geometricTailWitnessPackage_ising_predictedExponent_eq_rg :
    ((geometricTailWitnessPackage.retarget
      Ising3DModel).certificate).predictedExponent =
      (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent := by
  rw [InfiniteTailWitnessPackage.retarget_predictedExponent]
  rw [geometricTailWitnessPackage.certificate_predictedExponent_eq]
  rw [RGCertificate.retarget_predictedExponent]
  rw [halfThirdScalingRGCertificate_predictedExponent_eq]
  simp [predictedNu, BlockScale.toReal, exampleScale,
    halfThirdScalingBlockScale, FiniteWitnessPackageExample.exampleScale,
    geometricTailWitnessPackage]



theorem zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg :
    ((zeroTableClosedBallRGPackage.tableWitness.retarget
      Ising3DModel).certificate).predictedExponent =
      (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent := by
  rw [InfiniteTailTableWitnessPackage.retarget_predictedExponent]
  rw [InfiniteTailTableWitnessPackage.certificate_predictedExponent_eq]
  change predictedNu FiniteWitnessPackageExample.exampleScale 3 =
    (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent
  rw [RGCertificate.retarget_predictedExponent]
  rw [halfThirdScalingRGCertificate_predictedExponent_eq]
  simp [predictedNu, BlockScale.toReal, exampleScale,
    halfThirdScalingBlockScale, FiniteWitnessPackageExample.exampleScale]

end PackageExponentMatchingExample
end Exact3D
end StatMech

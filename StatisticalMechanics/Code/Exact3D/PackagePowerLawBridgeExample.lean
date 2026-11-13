/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.WitnessPowerLawBridge
import Code.Exact3D.FinitePlusTailPowerLawBridge
import Code.Exact3D.TableClosedBallPowerLawBridge
import Code.Exact3D.PackageComparisonBridgeExample








namespace StatMech
namespace Exact3D
namespace PackagePowerLawBridgeExample

open PackageComparisonBridgeExample
open FiniteWitnessPackageExample
open FinitePlusTailContractionExample
open InfiniteTailWitnessPackageExample



noncomputable def contributionSplitWitnessPowerLawCorrelationLength
    (β : ℝ) : ℝ :=
  Real.exp
    (-contributionSplitWitnessPackage.certificate.predictedExponent *
      Real.log ((ToyCriticalModel exampleScale 3).betaC - β))



theorem contributionSplitWitnessPowerLawCorrelationLength_exact_power :
    ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC
        (Set.Iio (ToyCriticalModel exampleScale 3).betaC),
      contributionSplitWitnessPowerLawCorrelationLength β =
        (1 : ℝ) *
          Real.exp
            (-contributionSplitWitnessPackage.certificate.predictedExponent *
              Real.log ((ToyCriticalModel exampleScale 3).betaC - β)) :=
  Filter.Eventually.of_forall fun _ => by
    simp [contributionSplitWitnessPowerLawCorrelationLength]



theorem contributionSplitWitness_bridge_from_powerLaw_wrapper :
    contributionSplitWitnessPackage.certificate.RGToExponentBridge
      contributionSplitWitnessPowerLawCorrelationLength :=
  contributionSplitWitnessPackage.rgToExponentBridge_of_eventually_exact_power_prefactor
    contributionSplitWitnessPowerLawCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    contributionSplitWitnessPowerLawCorrelationLength_exact_power



theorem contributionSplitWitness_bridge_from_variablePowerLaw_wrapper :
    contributionSplitWitnessPackage.certificate.RGToExponentBridge
      contributionSplitWitnessPowerLawCorrelationLength :=
  contributionSplitWitnessPackage
    |>.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      contributionSplitWitnessPowerLawCorrelationLength
      (fun _ : ℝ => (1 : ℝ))
      (Filter.Eventually.of_forall fun _ => by norm_num)
      (by simp)
      contributionSplitWitnessPowerLawCorrelationLength_exact_power



theorem contributionSplitWitness_bridge_from_powerLaw_on_Ioo :
    contributionSplitWitnessPackage.certificate.RGToExponentBridge
      contributionSplitWitnessPowerLawCorrelationLength :=
  contributionSplitWitnessPackage
    |>.rgToExponentBridge_of_exact_power_prefactor_on_Ioo
      contributionSplitWitnessPowerLawCorrelationLength
      1
      (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        simp [contributionSplitWitnessPowerLawCorrelationLength])



theorem contributionSplitWitness_bridge_from_variablePowerLaw_on_Ioo :
    contributionSplitWitnessPackage.certificate.RGToExponentBridge
      contributionSplitWitnessPowerLawCorrelationLength :=
  contributionSplitWitnessPackage
    |>.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
      contributionSplitWitnessPowerLawCorrelationLength
      (fun _ : ℝ => (1 : ℝ))
      1
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num)
      (by simp)
      (by
        intro β _hβ
        simp [contributionSplitWitnessPowerLawCorrelationLength])



theorem contributionSplitWitness_bridge_from_powerLaw_congr_pred :
    contributionSplitWitnessPackage.certificate.RGToExponentBridge
      contributionSplitWitnessPowerLawCorrelationLength :=
  contributionSplitWitnessPackage
    |>.rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent
      (D := contributionSplitWitnessPackage.certificate)
      contributionSplitWitnessPowerLawCorrelationLength
      rfl
      (by norm_num : (0 : ℝ) < 1)
      contributionSplitWitnessPowerLawCorrelationLength_exact_power



theorem contributionSplitWitness_bridge_from_variablePowerLaw_congr_pred :
    contributionSplitWitnessPackage.certificate.RGToExponentBridge
      contributionSplitWitnessPowerLawCorrelationLength :=
  contributionSplitWitnessPackage
    |>.rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
      (D := contributionSplitWitnessPackage.certificate)
      contributionSplitWitnessPowerLawCorrelationLength
      (fun _ : ℝ => (1 : ℝ))
      rfl
      (Filter.Eventually.of_forall fun _ => by norm_num)
      (by simp)
      contributionSplitWitnessPowerLawCorrelationLength_exact_power



theorem contributionSplitWitness_bridge_from_massPowerLaw_on_Ioo :
    contributionSplitWitnessPackage.certificate.RGToExponentBridge
      contributionSplitWitnessPowerLawCorrelationLength :=
  contributionSplitWitnessPackage
    |>.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
      contributionSplitWitnessPowerLawCorrelationLength
      (fun β : ℝ =>
        Real.exp
          (contributionSplitWitnessPackage.certificate.predictedExponent *
            Real.log ((ToyCriticalModel exampleScale 3).betaC - β)))
      (fun _ : ℝ => (1 : ℝ))
      1
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num)
      (by simp)
      (by
        intro β _hβ
        simp)
      (by
        intro β _hβ
        unfold contributionSplitWitnessPowerLawCorrelationLength
        rw [show
            -contributionSplitWitnessPackage.certificate.predictedExponent *
                Real.log ((ToyCriticalModel exampleScale 3).betaC - β) =
              -(contributionSplitWitnessPackage.certificate.predictedExponent *
                Real.log ((ToyCriticalModel exampleScale 3).betaC - β)) by
            ring,
          Real.exp_neg])



theorem contributionSplitWitness_bridge_from_powerLaw_on_Ioo_congr_pred :
    contributionSplitWitnessPackage.certificate.RGToExponentBridge
      contributionSplitWitnessPowerLawCorrelationLength :=
  contributionSplitWitnessPackage
    |>.rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
      (D := contributionSplitWitnessPackage.certificate)
      contributionSplitWitnessPowerLawCorrelationLength
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        simp [contributionSplitWitnessPowerLawCorrelationLength])



theorem
    contributionSplitWitness_bridge_from_variablePowerLaw_on_Ioo_congr_pred :
    contributionSplitWitnessPackage.certificate.RGToExponentBridge
      contributionSplitWitnessPowerLawCorrelationLength :=
  contributionSplitWitnessPackage
    |>.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
      (D := contributionSplitWitnessPackage.certificate)
      contributionSplitWitnessPowerLawCorrelationLength
      (fun _ : ℝ => (1 : ℝ))
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num)
      (by simp)
      (by
        intro β _hβ
        simp [contributionSplitWitnessPowerLawCorrelationLength])



theorem contributionSplitWitness_bridge_from_massPowerLaw_on_Ioo_congr_pred :
    contributionSplitWitnessPackage.certificate.RGToExponentBridge
      contributionSplitWitnessPowerLawCorrelationLength :=
  contributionSplitWitnessPackage
    |>.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
      (D := contributionSplitWitnessPackage.certificate)
      contributionSplitWitnessPowerLawCorrelationLength
      (fun β : ℝ =>
        Real.exp
          (contributionSplitWitnessPackage.certificate.predictedExponent *
            Real.log ((ToyCriticalModel exampleScale 3).betaC - β)))
      (fun _ : ℝ => (1 : ℝ))
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num)
      (by simp)
      (by
        intro β _hβ
        simp)
      (by
        intro β _hβ
        unfold contributionSplitWitnessPowerLawCorrelationLength
        rw [show
            -contributionSplitWitnessPackage.certificate.predictedExponent *
                Real.log ((ToyCriticalModel exampleScale 3).betaC - β) =
              -(contributionSplitWitnessPackage.certificate.predictedExponent *
                Real.log ((ToyCriticalModel exampleScale 3).betaC - β)) by
            ring,
          Real.exp_neg])



theorem contributionSplitWitness_valid_from_powerLaw_on_Ioo_congr_pred :
    contributionSplitWitnessPackage.certificate.Valid
      contributionSplitWitnessPowerLawCorrelationLength :=
  contributionSplitWitnessPackage
    |>.valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
      (D := contributionSplitWitnessPackage.certificate)
      contributionSplitWitnessPowerLawCorrelationLength
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        simp [contributionSplitWitnessPowerLawCorrelationLength])



theorem contributionSplitWitness_hasCriticalNu_from_powerLaw_on_Ioo_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      contributionSplitWitnessPowerLawCorrelationLength
      contributionSplitWitnessPackage.certificate.predictedExponent :=
  contributionSplitWitnessPackage
    |>.hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
      (D := contributionSplitWitnessPackage.certificate)
      contributionSplitWitnessPowerLawCorrelationLength
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        simp [contributionSplitWitnessPowerLawCorrelationLength])



theorem
    contributionSplitWitness_valid_from_variablePowerLaw_on_Ioo_congr_pred :
    contributionSplitWitnessPackage.certificate.Valid
      contributionSplitWitnessPowerLawCorrelationLength :=
  contributionSplitWitnessPackage
    |>.valid_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
      (D := contributionSplitWitnessPackage.certificate)
      contributionSplitWitnessPowerLawCorrelationLength
      (fun _ : ℝ => (1 : ℝ))
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num)
      (by simp)
      (by
        intro β _hβ
        simp [contributionSplitWitnessPowerLawCorrelationLength])



theorem
    contributionSplitWitness_hasCriticalNu_from_variablePowerLaw_on_Ioo_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      contributionSplitWitnessPowerLawCorrelationLength
      contributionSplitWitnessPackage.certificate.predictedExponent :=
  contributionSplitWitnessPackage
    |>.hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
      (D := contributionSplitWitnessPackage.certificate)
      contributionSplitWitnessPowerLawCorrelationLength
      (fun _ : ℝ => (1 : ℝ))
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num)
      (by simp)
      (by
        intro β _hβ
        simp [contributionSplitWitnessPowerLawCorrelationLength])



theorem contributionSplitWitness_valid_from_massPowerLaw_on_Ioo_congr_pred :
    contributionSplitWitnessPackage.certificate.Valid
      contributionSplitWitnessPowerLawCorrelationLength :=
  contributionSplitWitnessPackage
    |>.valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
      (D := contributionSplitWitnessPackage.certificate)
      contributionSplitWitnessPowerLawCorrelationLength
      (fun β : ℝ =>
        Real.exp
          (contributionSplitWitnessPackage.certificate.predictedExponent *
            Real.log ((ToyCriticalModel exampleScale 3).betaC - β)))
      (fun _ : ℝ => (1 : ℝ))
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num)
      (by simp)
      (by
        intro β _hβ
        simp)
      (by
        intro β _hβ
        unfold contributionSplitWitnessPowerLawCorrelationLength
        rw [show
            -contributionSplitWitnessPackage.certificate.predictedExponent *
                Real.log ((ToyCriticalModel exampleScale 3).betaC - β) =
              -(contributionSplitWitnessPackage.certificate.predictedExponent *
                Real.log ((ToyCriticalModel exampleScale 3).betaC - β)) by
            ring,
          Real.exp_neg])



theorem contributionSplitWitness_hasCriticalNu_from_massPowerLaw_on_Ioo_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      contributionSplitWitnessPowerLawCorrelationLength
      contributionSplitWitnessPackage.certificate.predictedExponent :=
  contributionSplitWitnessPackage
    |>.hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
      (D := contributionSplitWitnessPackage.certificate)
      contributionSplitWitnessPowerLawCorrelationLength
      (fun β : ℝ =>
        Real.exp
          (contributionSplitWitnessPackage.certificate.predictedExponent *
            Real.log ((ToyCriticalModel exampleScale 3).betaC - β)))
      (fun _ : ℝ => (1 : ℝ))
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num)
      (by simp)
      (by
        intro β _hβ
        simp)
      (by
        intro β _hβ
        unfold contributionSplitWitnessPowerLawCorrelationLength
        rw [show
            -contributionSplitWitnessPackage.certificate.predictedExponent *
                Real.log ((ToyCriticalModel exampleScale 3).betaC - β) =
              -(contributionSplitWitnessPackage.certificate.predictedExponent *
                Real.log ((ToyCriticalModel exampleScale 3).betaC - β)) by
            ring,
          Real.exp_neg])



theorem contributionSplitWitness_valid_from_powerLaw_wrapper :
    contributionSplitWitnessPackage.certificate.Valid
      contributionSplitWitnessPowerLawCorrelationLength :=
  contributionSplitWitnessPackage.valid_of_eventually_exact_power_prefactor
    contributionSplitWitnessPowerLawCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    contributionSplitWitnessPowerLawCorrelationLength_exact_power



theorem contributionSplitWitness_hasCriticalNu_from_powerLaw_wrapper :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      contributionSplitWitnessPowerLawCorrelationLength
      contributionSplitWitnessPackage.certificate.predictedExponent :=
  contributionSplitWitnessPackage.hasCriticalNu_of_eventually_exact_power_prefactor
    contributionSplitWitnessPowerLawCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    contributionSplitWitnessPowerLawCorrelationLength_exact_power



theorem contributionSplitWitness_valid_from_variablePowerLaw_wrapper :
    contributionSplitWitnessPackage.certificate.Valid
      contributionSplitWitnessPowerLawCorrelationLength :=
  contributionSplitWitnessPackage
    |>.valid_of_eventually_exact_power_variable_prefactor
      contributionSplitWitnessPowerLawCorrelationLength
      (fun _ : ℝ => (1 : ℝ))
      (Filter.Eventually.of_forall fun _ => by norm_num)
      (by simp)
      contributionSplitWitnessPowerLawCorrelationLength_exact_power



theorem contributionSplitWitness_hasCriticalNu_from_variablePowerLaw_wrapper :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      contributionSplitWitnessPowerLawCorrelationLength
      contributionSplitWitnessPackage.certificate.predictedExponent :=
  contributionSplitWitnessPackage
    |>.hasCriticalNu_of_eventually_exact_power_variable_prefactor
      contributionSplitWitnessPowerLawCorrelationLength
      (fun _ : ℝ => (1 : ℝ))
      (Filter.Eventually.of_forall fun _ => by norm_num)
      (by simp)
      contributionSplitWitnessPowerLawCorrelationLength_exact_power



theorem geometricTailWitness_bridge_from_powerLaw_wrapper :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      geometricTailCorrelationLength :=
  geometricTailWitnessPackage.rgToExponentBridge_of_eventually_exact_power_prefactor
    geometricTailCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [geometricTailCorrelationLength_exact_power] with β hβ
      simpa using hβ)



theorem geometricTailWitness_bridge_from_variablePowerLaw_wrapper :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      geometricTailCorrelationLength :=
  geometricTailWitnessPackage
    |>.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      geometricTailCorrelationLength
      (fun _ : ℝ => (1 : ℝ))
      (Filter.Eventually.of_forall fun _ => by norm_num)
      (by simp)
      (by
        filter_upwards [geometricTailCorrelationLength_exact_power] with β hβ
        simpa using hβ)



theorem geometricTailWitness_bridge_from_powerLaw_on_Ioo :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      geometricTailCorrelationLength :=
  geometricTailWitnessPackage
    |>.rgToExponentBridge_of_exact_power_prefactor_on_Ioo
      geometricTailCorrelationLength
      1
      (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        simp [geometricTailCorrelationLength])



theorem geometricTailWitness_bridge_from_variablePowerLaw_on_Ioo :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      geometricTailCorrelationLength :=
  geometricTailWitnessPackage
    |>.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
      geometricTailCorrelationLength
      (fun _ : ℝ => (1 : ℝ))
      1
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num)
      (by simp)
      (by
        intro β _hβ
        simp [geometricTailCorrelationLength])



theorem geometricTailWitness_bridge_from_powerLaw_congr_pred :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      geometricTailCorrelationLength :=
  geometricTailWitnessPackage
    |>.rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent
      (D := geometricTailWitnessPackage.certificate)
      geometricTailCorrelationLength
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by
        filter_upwards [geometricTailCorrelationLength_exact_power] with β hβ
        simpa using hβ)



theorem geometricTailWitness_bridge_from_variablePowerLaw_congr_pred :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      geometricTailCorrelationLength :=
  geometricTailWitnessPackage
    |>.rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
      (D := geometricTailWitnessPackage.certificate)
      geometricTailCorrelationLength
      (fun _ : ℝ => (1 : ℝ))
      rfl
      (Filter.Eventually.of_forall fun _ => by norm_num)
      (by simp)
      (by
        filter_upwards [geometricTailCorrelationLength_exact_power] with β hβ
        simpa using hβ)



theorem geometricTailWitness_bridge_from_massPowerLaw_on_Ioo :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      geometricTailCorrelationLength :=
  geometricTailWitnessPackage
    |>.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
      geometricTailCorrelationLength
      (fun β : ℝ =>
        Real.exp
          (geometricTailWitnessPackage.certificate.predictedExponent *
            Real.log ((ToyCriticalModel exampleScale 3).betaC - β)))
      (fun _ : ℝ => (1 : ℝ))
      1
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num)
      (by simp)
      (by
        intro β _hβ
        simp)
      (by
        intro β _hβ
        unfold geometricTailCorrelationLength
        rw [show
            -geometricTailWitnessPackage.certificate.predictedExponent *
                Real.log ((ToyCriticalModel exampleScale 3).betaC - β) =
              -(geometricTailWitnessPackage.certificate.predictedExponent *
                Real.log ((ToyCriticalModel exampleScale 3).betaC - β)) by
            ring,
          Real.exp_neg])



theorem geometricTailWitness_bridge_from_powerLaw_on_Ioo_congr_pred :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      geometricTailCorrelationLength :=
  geometricTailWitnessPackage
    |>.rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
      (D := geometricTailWitnessPackage.certificate)
      geometricTailCorrelationLength
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        simp [geometricTailCorrelationLength])



theorem geometricTailWitness_bridge_from_variablePowerLaw_on_Ioo_congr_pred :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      geometricTailCorrelationLength :=
  geometricTailWitnessPackage
    |>.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
      (D := geometricTailWitnessPackage.certificate)
      geometricTailCorrelationLength
      (fun _ : ℝ => (1 : ℝ))
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num)
      (by simp)
      (by
        intro β _hβ
        simp [geometricTailCorrelationLength])



theorem geometricTailWitness_bridge_from_massPowerLaw_on_Ioo_congr_pred :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      geometricTailCorrelationLength :=
  geometricTailWitnessPackage
    |>.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
      (D := geometricTailWitnessPackage.certificate)
      geometricTailCorrelationLength
      (fun β : ℝ =>
        Real.exp
          (geometricTailWitnessPackage.certificate.predictedExponent *
            Real.log ((ToyCriticalModel exampleScale 3).betaC - β)))
      (fun _ : ℝ => (1 : ℝ))
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num)
      (by simp)
      (by
        intro β _hβ
        simp)
      (by
        intro β _hβ
        unfold geometricTailCorrelationLength
        rw [show
            -geometricTailWitnessPackage.certificate.predictedExponent *
                Real.log ((ToyCriticalModel exampleScale 3).betaC - β) =
              -(geometricTailWitnessPackage.certificate.predictedExponent *
                Real.log ((ToyCriticalModel exampleScale 3).betaC - β)) by
            ring,
          Real.exp_neg])



theorem geometricTailWitness_valid_from_powerLaw_on_Ioo_congr_pred :
    geometricTailWitnessPackage.certificate.Valid
      geometricTailCorrelationLength :=
  geometricTailWitnessPackage
    |>.valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
      (D := geometricTailWitnessPackage.certificate)
      geometricTailCorrelationLength
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        simp [geometricTailCorrelationLength])



theorem geometricTailWitness_hasCriticalNu_from_powerLaw_on_Ioo_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      geometricTailCorrelationLength
      geometricTailWitnessPackage.certificate.predictedExponent :=
  geometricTailWitnessPackage
    |>.hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
      (D := geometricTailWitnessPackage.certificate)
      geometricTailCorrelationLength
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        simp [geometricTailCorrelationLength])



theorem geometricTailWitness_valid_from_variablePowerLaw_on_Ioo_congr_pred :
    geometricTailWitnessPackage.certificate.Valid
      geometricTailCorrelationLength :=
  geometricTailWitnessPackage
    |>.valid_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
      (D := geometricTailWitnessPackage.certificate)
      geometricTailCorrelationLength
      (fun _ : ℝ => (1 : ℝ))
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num)
      (by simp)
      (by
        intro β _hβ
        simp [geometricTailCorrelationLength])



theorem
    geometricTailWitness_hasCriticalNu_from_variablePowerLaw_on_Ioo_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      geometricTailCorrelationLength
      geometricTailWitnessPackage.certificate.predictedExponent :=
  geometricTailWitnessPackage
    |>.hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
      (D := geometricTailWitnessPackage.certificate)
      geometricTailCorrelationLength
      (fun _ : ℝ => (1 : ℝ))
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num)
      (by simp)
      (by
        intro β _hβ
        simp [geometricTailCorrelationLength])



theorem geometricTailWitness_valid_from_massPowerLaw_on_Ioo_congr_pred :
    geometricTailWitnessPackage.certificate.Valid
      geometricTailCorrelationLength :=
  geometricTailWitnessPackage
    |>.valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
      (D := geometricTailWitnessPackage.certificate)
      geometricTailCorrelationLength
      (fun β : ℝ =>
        Real.exp
          (geometricTailWitnessPackage.certificate.predictedExponent *
            Real.log ((ToyCriticalModel exampleScale 3).betaC - β)))
      (fun _ : ℝ => (1 : ℝ))
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num)
      (by simp)
      (by
        intro β _hβ
        simp)
      (by
        intro β _hβ
        unfold geometricTailCorrelationLength
        rw [show
            -geometricTailWitnessPackage.certificate.predictedExponent *
                Real.log ((ToyCriticalModel exampleScale 3).betaC - β) =
              -(geometricTailWitnessPackage.certificate.predictedExponent *
                Real.log ((ToyCriticalModel exampleScale 3).betaC - β)) by
            ring,
          Real.exp_neg])



theorem geometricTailWitness_hasCriticalNu_from_massPowerLaw_on_Ioo_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      geometricTailCorrelationLength
      geometricTailWitnessPackage.certificate.predictedExponent :=
  geometricTailWitnessPackage
    |>.hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
      (D := geometricTailWitnessPackage.certificate)
      geometricTailCorrelationLength
      (fun β : ℝ =>
        Real.exp
          (geometricTailWitnessPackage.certificate.predictedExponent *
            Real.log ((ToyCriticalModel exampleScale 3).betaC - β)))
      (fun _ : ℝ => (1 : ℝ))
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num)
      (by simp)
      (by
        intro β _hβ
        simp)
      (by
        intro β _hβ
        unfold geometricTailCorrelationLength
        rw [show
            -geometricTailWitnessPackage.certificate.predictedExponent *
                Real.log ((ToyCriticalModel exampleScale 3).betaC - β) =
              -(geometricTailWitnessPackage.certificate.predictedExponent *
                Real.log ((ToyCriticalModel exampleScale 3).betaC - β)) by
            ring,
          Real.exp_neg])



theorem geometricTailWitness_valid_from_powerLaw_wrapper :
    geometricTailWitnessPackage.certificate.Valid
      geometricTailCorrelationLength :=
  geometricTailWitnessPackage.valid_of_eventually_exact_power_prefactor
    geometricTailCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [geometricTailCorrelationLength_exact_power] with β hβ
      simpa using hβ)



theorem geometricTailWitness_hasCriticalNu_from_powerLaw_wrapper :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      geometricTailCorrelationLength
      geometricTailWitnessPackage.certificate.predictedExponent :=
  geometricTailWitnessPackage.hasCriticalNu_of_eventually_exact_power_prefactor
    geometricTailCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [geometricTailCorrelationLength_exact_power] with β hβ
      simpa using hβ)



theorem geometricTailWitness_valid_from_variablePowerLaw_wrapper :
    geometricTailWitnessPackage.certificate.Valid
      geometricTailCorrelationLength :=
  geometricTailWitnessPackage
    |>.valid_of_eventually_exact_power_variable_prefactor
      geometricTailCorrelationLength
      (fun _ : ℝ => (1 : ℝ))
      (Filter.Eventually.of_forall fun _ => by norm_num)
      (by simp)
      (by
        filter_upwards [geometricTailCorrelationLength_exact_power] with β hβ
        simpa using hβ)



theorem geometricTailWitness_hasCriticalNu_from_variablePowerLaw_wrapper :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      geometricTailCorrelationLength
      geometricTailWitnessPackage.certificate.predictedExponent :=
  geometricTailWitnessPackage
    |>.hasCriticalNu_of_eventually_exact_power_variable_prefactor
      geometricTailCorrelationLength
      (fun _ : ℝ => (1 : ℝ))
      (Filter.Eventually.of_forall fun _ => by norm_num)
      (by simp)
      (by
        filter_upwards [geometricTailCorrelationLength_exact_power] with β hβ
        simpa using hβ)



theorem zeroStableKeyTableWitness_bridge_from_powerLaw_wrapper :
    zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge
      zeroStableKeyTableWitnessCorrelationLength :=
  zeroStableKeyTableWitnessPackage.rgToExponentBridge_of_eventually_exact_power_prefactor
    zeroStableKeyTableWitnessCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [zeroStableKeyTableWitnessCorrelationLength_exact_power]
        with β hβ
      simpa using hβ)



theorem zeroStableKeyTableWitness_bridge_from_variablePowerLaw_wrapper :
    zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge
      zeroStableKeyTableWitnessCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
      zeroStableKeyTableWitnessCorrelationLength
      (fun _ : ℝ => (1 : ℝ))
      (Filter.Eventually.of_forall fun _ => by norm_num)
      (by simp)
      (by
        filter_upwards [zeroStableKeyTableWitnessCorrelationLength_exact_power]
          with β hβ
        simpa using hβ)



theorem zeroStableKeyTableWitness_bridge_from_powerLaw_on_Ioo :
    zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge
      zeroStableKeyTableWitnessCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.rgToExponentBridge_of_exact_power_prefactor_on_Ioo
      zeroStableKeyTableWitnessCorrelationLength
      1
      (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        simp [zeroStableKeyTableWitnessCorrelationLength])



theorem zeroStableKeyTableWitness_bridge_from_variablePowerLaw_on_Ioo :
    zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge
      zeroStableKeyTableWitnessCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
      zeroStableKeyTableWitnessCorrelationLength
      (fun _ : ℝ => (1 : ℝ))
      1
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num)
      (by simp)
      (by
        intro β _hβ
        simp [zeroStableKeyTableWitnessCorrelationLength])



theorem zeroStableKeyTableWitness_bridge_from_powerLaw_congr_pred :
    zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge
      zeroStableKeyTableWitnessCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent
      (D := zeroStableKeyTableWitnessPackage.certificate)
      zeroStableKeyTableWitnessCorrelationLength
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by
        filter_upwards [zeroStableKeyTableWitnessCorrelationLength_exact_power]
          with β hβ
        simpa using hβ)



theorem zeroStableKeyTableWitness_bridge_from_variablePowerLaw_congr_pred :
    zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge
      zeroStableKeyTableWitnessCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
      (D := zeroStableKeyTableWitnessPackage.certificate)
      zeroStableKeyTableWitnessCorrelationLength
      (fun _ : ℝ => (1 : ℝ))
      rfl
      (Filter.Eventually.of_forall fun _ => by norm_num)
      (by simp)
      (by
        filter_upwards [zeroStableKeyTableWitnessCorrelationLength_exact_power]
          with β hβ
        simpa using hβ)



theorem zeroStableKeyTableWitness_bridge_from_massPowerLaw_on_Ioo :
    zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge
      zeroStableKeyTableWitnessCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
      zeroStableKeyTableWitnessCorrelationLength
      (fun β : ℝ =>
        Real.exp
          (zeroStableKeyTableWitnessPackage.certificate.predictedExponent *
            Real.log ((ToyCriticalModel exampleScale 3).betaC - β)))
      (fun _ : ℝ => (1 : ℝ))
      1
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num)
      (by simp)
      (by
        intro β _hβ
        simp)
      (by
        intro β _hβ
        unfold zeroStableKeyTableWitnessCorrelationLength
        rw [show
            -zeroStableKeyTableWitnessPackage.certificate.predictedExponent *
                Real.log ((ToyCriticalModel exampleScale 3).betaC - β) =
              -(zeroStableKeyTableWitnessPackage.certificate.predictedExponent *
                Real.log ((ToyCriticalModel exampleScale 3).betaC - β)) by
            ring,
          Real.exp_neg])



theorem zeroStableKeyTableWitness_bridge_from_powerLaw_on_Ioo_congr_pred :
    zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge
      zeroStableKeyTableWitnessCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
      (D := zeroStableKeyTableWitnessPackage.certificate)
      zeroStableKeyTableWitnessCorrelationLength
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        simp [zeroStableKeyTableWitnessCorrelationLength])



theorem
    zeroStableKeyTableWitness_bridge_from_variablePowerLaw_on_Ioo_congr_pred :
    zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge
      zeroStableKeyTableWitnessCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
      (D := zeroStableKeyTableWitnessPackage.certificate)
      zeroStableKeyTableWitnessCorrelationLength
      (fun _ : ℝ => (1 : ℝ))
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num)
      (by simp)
      (by
        intro β _hβ
        simp [zeroStableKeyTableWitnessCorrelationLength])



theorem zeroStableKeyTableWitness_bridge_from_massPowerLaw_on_Ioo_congr_pred :
    zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge
      zeroStableKeyTableWitnessCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
      (D := zeroStableKeyTableWitnessPackage.certificate)
      zeroStableKeyTableWitnessCorrelationLength
      (fun β : ℝ =>
        Real.exp
          (zeroStableKeyTableWitnessPackage.certificate.predictedExponent *
            Real.log ((ToyCriticalModel exampleScale 3).betaC - β)))
      (fun _ : ℝ => (1 : ℝ))
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num)
      (by simp)
      (by
        intro β _hβ
        simp)
      (by
        intro β _hβ
        unfold zeroStableKeyTableWitnessCorrelationLength
        rw [show
            -zeroStableKeyTableWitnessPackage.certificate.predictedExponent *
                Real.log ((ToyCriticalModel exampleScale 3).betaC - β) =
              -(zeroStableKeyTableWitnessPackage.certificate.predictedExponent *
                Real.log ((ToyCriticalModel exampleScale 3).betaC - β)) by
            ring,
          Real.exp_neg])



theorem zeroStableKeyTableWitness_valid_from_powerLaw_on_Ioo_congr_pred :
    zeroStableKeyTableWitnessPackage.certificate.Valid
      zeroStableKeyTableWitnessCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
      (D := zeroStableKeyTableWitnessPackage.certificate)
      zeroStableKeyTableWitnessCorrelationLength
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        simp [zeroStableKeyTableWitnessCorrelationLength])



theorem
    zeroStableKeyTableWitness_hasCriticalNu_from_powerLaw_on_Ioo_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroStableKeyTableWitnessCorrelationLength
      zeroStableKeyTableWitnessPackage.certificate.predictedExponent :=
  zeroStableKeyTableWitnessPackage
    |>.hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
      (D := zeroStableKeyTableWitnessPackage.certificate)
      zeroStableKeyTableWitnessCorrelationLength
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        simp [zeroStableKeyTableWitnessCorrelationLength])



theorem
    zeroStableKeyTableWitness_valid_from_variablePowerLaw_on_Ioo_congr_pred :
    zeroStableKeyTableWitnessPackage.certificate.Valid
      zeroStableKeyTableWitnessCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.valid_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
      (D := zeroStableKeyTableWitnessPackage.certificate)
      zeroStableKeyTableWitnessCorrelationLength
      (fun _ : ℝ => (1 : ℝ))
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num)
      (by simp)
      (by
        intro β _hβ
        simp [zeroStableKeyTableWitnessCorrelationLength])



theorem
    zeroStableKeyTableWitness_hasCriticalNu_from_variablePowerLaw_on_Ioo_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroStableKeyTableWitnessCorrelationLength
      zeroStableKeyTableWitnessPackage.certificate.predictedExponent :=
  zeroStableKeyTableWitnessPackage
    |>.hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent
      (D := zeroStableKeyTableWitnessPackage.certificate)
      zeroStableKeyTableWitnessCorrelationLength
      (fun _ : ℝ => (1 : ℝ))
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num)
      (by simp)
      (by
        intro β _hβ
        simp [zeroStableKeyTableWitnessCorrelationLength])



theorem zeroStableKeyTableWitness_valid_from_massPowerLaw_on_Ioo_congr_pred :
    zeroStableKeyTableWitnessPackage.certificate.Valid
      zeroStableKeyTableWitnessCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
      (D := zeroStableKeyTableWitnessPackage.certificate)
      zeroStableKeyTableWitnessCorrelationLength
      (fun β : ℝ =>
        Real.exp
          (zeroStableKeyTableWitnessPackage.certificate.predictedExponent *
            Real.log ((ToyCriticalModel exampleScale 3).betaC - β)))
      (fun _ : ℝ => (1 : ℝ))
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num)
      (by simp)
      (by
        intro β _hβ
        simp)
      (by
        intro β _hβ
        unfold zeroStableKeyTableWitnessCorrelationLength
        rw [show
            -zeroStableKeyTableWitnessPackage.certificate.predictedExponent *
                Real.log ((ToyCriticalModel exampleScale 3).betaC - β) =
              -(zeroStableKeyTableWitnessPackage.certificate.predictedExponent *
                Real.log ((ToyCriticalModel exampleScale 3).betaC - β)) by
            ring,
          Real.exp_neg])



theorem
    zeroStableKeyTableWitness_hasCriticalNu_from_massPowerLaw_on_Ioo_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroStableKeyTableWitnessCorrelationLength
      zeroStableKeyTableWitnessPackage.certificate.predictedExponent :=
  zeroStableKeyTableWitnessPackage
    |>.hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent
      (D := zeroStableKeyTableWitnessPackage.certificate)
      zeroStableKeyTableWitnessCorrelationLength
      (fun β : ℝ =>
        Real.exp
          (zeroStableKeyTableWitnessPackage.certificate.predictedExponent *
            Real.log ((ToyCriticalModel exampleScale 3).betaC - β)))
      (fun _ : ℝ => (1 : ℝ))
      1
      rfl
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num)
      (by simp)
      (by
        intro β _hβ
        simp)
      (by
        intro β _hβ
        unfold zeroStableKeyTableWitnessCorrelationLength
        rw [show
            -zeroStableKeyTableWitnessPackage.certificate.predictedExponent *
                Real.log ((ToyCriticalModel exampleScale 3).betaC - β) =
              -(zeroStableKeyTableWitnessPackage.certificate.predictedExponent *
                Real.log ((ToyCriticalModel exampleScale 3).betaC - β)) by
            ring,
          Real.exp_neg])



theorem zeroStableKeyTableWitness_valid_from_powerLaw_wrapper :
    zeroStableKeyTableWitnessPackage.certificate.Valid
      zeroStableKeyTableWitnessCorrelationLength :=
  zeroStableKeyTableWitnessPackage.valid_of_eventually_exact_power_prefactor
    zeroStableKeyTableWitnessCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [zeroStableKeyTableWitnessCorrelationLength_exact_power]
        with β hβ
      simpa using hβ)



theorem zeroStableKeyTableWitness_hasCriticalNu_from_powerLaw_wrapper :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroStableKeyTableWitnessCorrelationLength
      zeroStableKeyTableWitnessPackage.certificate.predictedExponent :=
  zeroStableKeyTableWitnessPackage.hasCriticalNu_of_eventually_exact_power_prefactor
    zeroStableKeyTableWitnessCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [zeroStableKeyTableWitnessCorrelationLength_exact_power]
        with β hβ
      simpa using hβ)



theorem zeroStableKeyTableWitness_valid_from_variablePowerLaw_wrapper :
    zeroStableKeyTableWitnessPackage.certificate.Valid
      zeroStableKeyTableWitnessCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.valid_of_eventually_exact_power_variable_prefactor
      zeroStableKeyTableWitnessCorrelationLength
      (fun _ : ℝ => (1 : ℝ))
      (Filter.Eventually.of_forall fun _ => by norm_num)
      (by simp)
      (by
        filter_upwards [zeroStableKeyTableWitnessCorrelationLength_exact_power]
          with β hβ
        simpa using hβ)



theorem zeroStableKeyTableWitness_hasCriticalNu_from_variablePowerLaw_wrapper :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroStableKeyTableWitnessCorrelationLength
      zeroStableKeyTableWitnessPackage.certificate.predictedExponent :=
  zeroStableKeyTableWitnessPackage
    |>.hasCriticalNu_of_eventually_exact_power_variable_prefactor
      zeroStableKeyTableWitnessCorrelationLength
      (fun _ : ℝ => (1 : ℝ))
      (Filter.Eventually.of_forall fun _ => by norm_num)
      (by simp)
      (by
        filter_upwards [zeroStableKeyTableWitnessCorrelationLength_exact_power]
          with β hβ
        simpa using hβ)

section HyperbolicExamples

open FinitePlusTailHyperbolicSplitting



theorem halfThirdScalingHyperbolic_bridge_from_powerLaw_wrapper :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_eventually_exact_power_prefactor
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [halfThirdScalingCorrelationLength_exact_power] with β hβ
      simpa [halfThirdScalingRGCertificate] using hβ)



theorem halfThirdScalingHyperbolic_valid_from_powerLaw_wrapper :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingCorrelationLength :=
  certificate_valid_of_eventually_exact_power_prefactor
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [halfThirdScalingCorrelationLength_exact_power] with β hβ
      simpa [halfThirdScalingRGCertificate] using hβ)



theorem halfThirdScalingHyperbolic_hasCriticalNu_from_powerLaw_wrapper :
    HasCriticalNu halfThirdScalingModel
      halfThirdScalingCorrelationLength
      (halfThirdScalingHyperbolicSplitting.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent :=
  certificate_hasCriticalNu_of_eventually_exact_power_prefactor
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [halfThirdScalingCorrelationLength_exact_power] with β hβ
      simpa [halfThirdScalingRGCertificate] using hβ)



theorem halfThirdScalingHyperbolic_bridge_from_variablePowerLaw_wrapper :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingCorrelationLength_prefactor_power]
        with β hβ
      simpa [halfThirdScalingRGCertificate] using hβ)



theorem halfThirdScalingHyperbolic_bridge_from_powerLaw_on_Ioo :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    1
    (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1)
    (by
      intro β _hβ
      simp [halfThirdScalingCorrelationLength, halfThirdScalingRGCertificate])



theorem halfThirdScalingHyperbolic_bridge_from_variablePowerLaw_on_Ioo :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    1
    (by norm_num : (0 : ℝ) < 1)
    (by
      intro β _hβ
      norm_num [halfThirdScalingPrefactor])
    halfThirdScalingPrefactor_log_negligible
    (by
      intro β _hβ
      simp [halfThirdScalingCorrelationLength, halfThirdScalingPrefactor,
        halfThirdScalingRGCertificate])



theorem halfThirdScalingHyperbolic_valid_from_variablePowerLaw_wrapper :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingCorrelationLength :=
  certificate_valid_of_eventually_exact_power_variable_prefactor
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingCorrelationLength_prefactor_power]
        with β hβ
      simpa [halfThirdScalingRGCertificate] using hβ)



theorem halfThirdScalingHyperbolic_hasCriticalNu_from_variablePowerLaw_wrapper :
    HasCriticalNu halfThirdScalingModel
      halfThirdScalingCorrelationLength
      (halfThirdScalingHyperbolicSplitting.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent :=
  certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingCorrelationLength_prefactor_power]
        with β hβ
      simpa [halfThirdScalingRGCertificate] using hβ)



theorem halfThirdScalingHyperbolic_bridge_from_massPowerLaw_wrapper :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingMass_power] with β hβ
      simpa [halfThirdScalingRGCertificate] using hβ)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem halfThirdScalingHyperbolic_bridge_from_massPowerLaw_on_Ioo :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    1
    (by norm_num : (0 : ℝ) < 1)
    (by
      intro β _hβ
      norm_num [halfThirdScalingMassPrefactor])
    halfThirdScalingMassPrefactor_log_negligible
    (by
      intro β _hβ
      simp [halfThirdScalingMass, halfThirdScalingMassPrefactor,
        halfThirdScalingRGCertificate])
    (by
      intro β _hβ
      unfold halfThirdScalingCorrelationLength halfThirdScalingMass
      rw [show
          -halfThirdScalingRGCertificate.predictedExponent *
              Real.log (halfThirdScalingModel.betaC - β) =
            -(halfThirdScalingRGCertificate.predictedExponent *
              Real.log (halfThirdScalingModel.betaC - β)) by
          ring,
        Real.exp_neg])



theorem halfThirdScalingHyperbolic_bridge_from_powerLaw_on_Ioo_congr_pred :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingModel
    (D := halfThirdScalingRGCertificate)
    halfThirdScalingCorrelationLength
    1
    rfl
    (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1)
    (by
      intro β _hβ
      simp [halfThirdScalingCorrelationLength])




theorem halfThirdScalingHyperbolic_bridge_from_variablePowerLaw_on_Ioo_congr_pred :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingModel
    (D := halfThirdScalingRGCertificate)
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    1
    rfl
    (by norm_num : (0 : ℝ) < 1)
    (by
      intro β _hβ
      norm_num [halfThirdScalingPrefactor])
    halfThirdScalingPrefactor_log_negligible
    (by
      intro β _hβ
      simp [halfThirdScalingCorrelationLength, halfThirdScalingPrefactor])



theorem halfThirdScalingHyperbolic_bridge_from_massPowerLaw_on_Ioo_congr_pred :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingModel
    (D := halfThirdScalingRGCertificate)
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    1
    rfl
    (by norm_num : (0 : ℝ) < 1)
    (by
      intro β _hβ
      norm_num [halfThirdScalingMassPrefactor])
    halfThirdScalingMassPrefactor_log_negligible
    (by
      intro β _hβ
      simp [halfThirdScalingMass, halfThirdScalingMassPrefactor])
    (by
      intro β _hβ
      unfold halfThirdScalingCorrelationLength halfThirdScalingMass
      rw [show
          -halfThirdScalingRGCertificate.predictedExponent *
              Real.log (halfThirdScalingModel.betaC - β) =
            -(halfThirdScalingRGCertificate.predictedExponent *
              Real.log (halfThirdScalingModel.betaC - β)) by
          ring,
        Real.exp_neg])



theorem halfThirdScalingHyperbolic_valid_from_massPowerLaw_wrapper :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingCorrelationLength :=
  certificate_valid_of_eventually_exact_mass_power_variable_prefactor
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingMass_power] with β hβ
      simpa [halfThirdScalingRGCertificate] using hβ)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem halfThirdScalingHyperbolic_hasCriticalNu_from_massPowerLaw_wrapper :
    HasCriticalNu halfThirdScalingModel
      halfThirdScalingCorrelationLength
      (halfThirdScalingHyperbolicSplitting.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent :=
  certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingMass_power] with β hβ
      simpa [halfThirdScalingRGCertificate] using hβ)
    halfThirdScalingCorrelationLength_eq_inv_mass

end HyperbolicExamples

section BlockRGExamples

open FinitePlusTailBlockRGPackage



theorem halfThirdScalingBlockRGPackage_bridge_from_powerLaw_wrapper :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_eventually_exact_power_prefactor
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [halfThirdScalingCorrelationLength_exact_power] with β hβ
      simpa [halfThirdScalingBlockRGCertificate,
        halfThirdScalingBlockRGCertificate_predictedExponent_eq_rg] using hβ)



theorem halfThirdScalingBlockRGPackage_valid_from_powerLaw_wrapper :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingCorrelationLength :=
  certificate_valid_of_eventually_exact_power_prefactor
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [halfThirdScalingCorrelationLength_exact_power] with β hβ
      simpa [halfThirdScalingBlockRGCertificate,
        halfThirdScalingBlockRGCertificate_predictedExponent_eq_rg] using hβ)



theorem halfThirdScalingBlockRGPackage_hasCriticalNu_from_powerLaw_wrapper :
    HasCriticalNu halfThirdScalingModel
      halfThirdScalingCorrelationLength
      (halfThirdScalingBlockRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent :=
  certificate_hasCriticalNu_of_eventually_exact_power_prefactor
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [halfThirdScalingCorrelationLength_exact_power] with β hβ
      simpa [halfThirdScalingBlockRGCertificate,
        halfThirdScalingBlockRGCertificate_predictedExponent_eq_rg] using hβ)



theorem halfThirdScalingBlockRGPackage_bridge_from_variablePowerLaw_wrapper :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingCorrelationLength_prefactor_power]
        with β hβ
      simpa [halfThirdScalingBlockRGCertificate,
        halfThirdScalingBlockRGCertificate_predictedExponent_eq_rg] using hβ)



theorem halfThirdScalingBlockRGPackage_bridge_from_powerLaw_on_Ioo :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    1
    (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1)
    (by
      intro β _hβ
      change halfThirdScalingCorrelationLength β =
        (1 : ℝ) * Real.exp
          (-halfThirdScalingBlockRGCertificate.predictedExponent *
            Real.log (halfThirdScalingModel.betaC - β))
      rw [halfThirdScalingBlockRGCertificate_predictedExponent_eq_rg]
      simp [halfThirdScalingCorrelationLength])



theorem halfThirdScalingBlockRGPackage_bridge_from_variablePowerLaw_on_Ioo :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    1
    (by norm_num : (0 : ℝ) < 1)
    (by
      intro β _hβ
      norm_num [halfThirdScalingPrefactor])
    halfThirdScalingPrefactor_log_negligible
    (by
      intro β _hβ
      change halfThirdScalingCorrelationLength β =
        halfThirdScalingPrefactor β *
          Real.exp
            (-halfThirdScalingBlockRGCertificate.predictedExponent *
              Real.log (halfThirdScalingModel.betaC - β))
      rw [halfThirdScalingBlockRGCertificate_predictedExponent_eq_rg]
      simp [halfThirdScalingCorrelationLength, halfThirdScalingPrefactor])



theorem halfThirdScalingBlockRGPackage_valid_from_variablePowerLaw_wrapper :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingCorrelationLength :=
  certificate_valid_of_eventually_exact_power_variable_prefactor
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingCorrelationLength_prefactor_power]
        with β hβ
      simpa [halfThirdScalingBlockRGCertificate,
        halfThirdScalingBlockRGCertificate_predictedExponent_eq_rg] using hβ)



theorem halfThirdScalingBlockRGPackage_hasCriticalNu_from_variablePowerLaw_wrapper :
    HasCriticalNu halfThirdScalingModel
      halfThirdScalingCorrelationLength
      (halfThirdScalingBlockRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent :=
  certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingCorrelationLength_prefactor_power]
        with β hβ
      simpa [halfThirdScalingBlockRGCertificate,
        halfThirdScalingBlockRGCertificate_predictedExponent_eq_rg] using hβ)



theorem halfThirdScalingBlockRGPackage_bridge_from_massPowerLaw_wrapper :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingMass_power] with β hβ
      simpa [halfThirdScalingBlockRGCertificate,
        halfThirdScalingBlockRGCertificate_predictedExponent_eq_rg] using hβ)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem halfThirdScalingBlockRGPackage_bridge_from_massPowerLaw_on_Ioo :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    1
    (by norm_num : (0 : ℝ) < 1)
    (by
      intro β _hβ
      norm_num [halfThirdScalingMassPrefactor])
    halfThirdScalingMassPrefactor_log_negligible
    (by
      intro β _hβ
      change halfThirdScalingMass β =
        halfThirdScalingMassPrefactor β *
          Real.exp
            (halfThirdScalingBlockRGCertificate.predictedExponent *
              Real.log (halfThirdScalingModel.betaC - β))
      rw [halfThirdScalingBlockRGCertificate_predictedExponent_eq_rg]
      simp [halfThirdScalingMass, halfThirdScalingMassPrefactor])
    (by
      intro β _hβ
      unfold halfThirdScalingCorrelationLength halfThirdScalingMass
      rw [show
          -halfThirdScalingRGCertificate.predictedExponent *
              Real.log (halfThirdScalingModel.betaC - β) =
            -(halfThirdScalingRGCertificate.predictedExponent *
              Real.log (halfThirdScalingModel.betaC - β)) by
          ring,
        Real.exp_neg])



theorem halfThirdScalingBlockRGPackage_bridge_from_powerLaw_on_Ioo_congr_pred :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    (D := halfThirdScalingRGCertificate)
    halfThirdScalingCorrelationLength
    1
    (by
      simpa [halfThirdScalingBlockRGCertificate] using
        halfThirdScalingBlockRGCertificate_predictedExponent_eq_rg)
    (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1)
    (by
      intro β _hβ
      simp [halfThirdScalingCorrelationLength])




theorem
    halfThirdScalingBlockRGPackage_bridge_from_variablePowerLaw_on_Ioo_congr_pred :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    (D := halfThirdScalingRGCertificate)
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    1
    (by
      simpa [halfThirdScalingBlockRGCertificate] using
        halfThirdScalingBlockRGCertificate_predictedExponent_eq_rg)
    (by norm_num : (0 : ℝ) < 1)
    (by
      intro β _hβ
      norm_num [halfThirdScalingPrefactor])
    halfThirdScalingPrefactor_log_negligible
    (by
      intro β _hβ
      simp [halfThirdScalingCorrelationLength, halfThirdScalingPrefactor])



theorem halfThirdScalingBlockRGPackage_bridge_from_massPowerLaw_on_Ioo_congr_pred :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    (D := halfThirdScalingRGCertificate)
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    1
    (by
      simpa [halfThirdScalingBlockRGCertificate] using
        halfThirdScalingBlockRGCertificate_predictedExponent_eq_rg)
    (by norm_num : (0 : ℝ) < 1)
    (by
      intro β _hβ
      norm_num [halfThirdScalingMassPrefactor])
    halfThirdScalingMassPrefactor_log_negligible
    (by
      intro β _hβ
      simp [halfThirdScalingMass, halfThirdScalingMassPrefactor])
    (by
      intro β _hβ
      unfold halfThirdScalingCorrelationLength halfThirdScalingMass
      rw [show
          -halfThirdScalingRGCertificate.predictedExponent *
              Real.log (halfThirdScalingModel.betaC - β) =
            -(halfThirdScalingRGCertificate.predictedExponent *
              Real.log (halfThirdScalingModel.betaC - β)) by
          ring,
        Real.exp_neg])



theorem halfThirdScalingBlockRGPackage_valid_from_massPowerLaw_wrapper :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingCorrelationLength :=
  certificate_valid_of_eventually_exact_mass_power_variable_prefactor
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingMass_power] with β hβ
      simpa [halfThirdScalingBlockRGCertificate,
        halfThirdScalingBlockRGCertificate_predictedExponent_eq_rg] using hβ)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem halfThirdScalingBlockRGPackage_hasCriticalNu_from_massPowerLaw_wrapper :
    HasCriticalNu halfThirdScalingModel
      halfThirdScalingCorrelationLength
      (halfThirdScalingBlockRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent :=
  certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingMass_power] with β hβ
      simpa [halfThirdScalingBlockRGCertificate,
        halfThirdScalingBlockRGCertificate_predictedExponent_eq_rg] using hβ)
    halfThirdScalingCorrelationLength_eq_inv_mass

end BlockRGExamples

section ClosedBallExamples

open FinitePlusTailClosedBallRGPackage



theorem halfThirdScalingClosedBall_predictedExponent_eq_rg :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent =
      halfThirdScalingRGCertificate.predictedExponent := by
  rw [halfThirdScalingUnitClosedBallRGPackage_predictedExponent_eq,
    halfThirdScalingRGCertificate_predictedExponent_eq]



theorem halfThirdScalingClosedBall_bridge_from_powerLaw_congr_pred :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingClosedBall_predictedExponent_eq_rg
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [halfThirdScalingCorrelationLength_exact_power] with β hβ
      simpa using hβ)



theorem halfThirdScalingClosedBall_valid_from_powerLaw_congr_pred :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingCorrelationLength :=
  certificate_valid_of_eventually_exact_power_prefactor_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingClosedBall_predictedExponent_eq_rg
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [halfThirdScalingCorrelationLength_exact_power] with β hβ
      simpa using hβ)



theorem halfThirdScalingClosedBall_hasCriticalNu_from_powerLaw_congr_pred :
    HasCriticalNu halfThirdScalingModel
      halfThirdScalingCorrelationLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent :=
  certificate_hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingClosedBall_predictedExponent_eq_rg
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [halfThirdScalingCorrelationLength_exact_power] with β hβ
      simpa using hβ)



theorem halfThirdScalingClosedBall_bridge_from_variablePowerLaw_congr_pred :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    halfThirdScalingClosedBall_predictedExponent_eq_rg
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingCorrelationLength_prefactor_power]
        with β hβ
      simpa using hβ)



theorem halfThirdScalingClosedBall_bridge_from_powerLaw_on_Ioo :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    1
    (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1)
    (by
      intro β _hβ
      rw [halfThirdScalingClosedBall_predictedExponent_eq_rg]
      simp [halfThirdScalingCorrelationLength])



theorem halfThirdScalingClosedBall_bridge_from_variablePowerLaw_on_Ioo :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    1
    (by norm_num : (0 : ℝ) < 1)
    (by
      intro β _hβ
      norm_num [halfThirdScalingPrefactor])
    halfThirdScalingPrefactor_log_negligible
    (by
      intro β _hβ
      rw [halfThirdScalingClosedBall_predictedExponent_eq_rg]
      simp [halfThirdScalingCorrelationLength, halfThirdScalingPrefactor])



theorem halfThirdScalingClosedBall_valid_from_variablePowerLaw_congr_pred :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingCorrelationLength :=
  certificate_valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    halfThirdScalingClosedBall_predictedExponent_eq_rg
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingCorrelationLength_prefactor_power]
        with β hβ
      simpa using hβ)



theorem halfThirdScalingClosedBall_hasCriticalNu_from_variablePowerLaw_congr_pred :
    HasCriticalNu halfThirdScalingModel
      halfThirdScalingCorrelationLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent :=
  certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    halfThirdScalingClosedBall_predictedExponent_eq_rg
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingCorrelationLength_prefactor_power]
        with β hβ
      simpa using hβ)



theorem halfThirdScalingClosedBall_bridge_from_massPowerLaw_congr_pred :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingClosedBall_predictedExponent_eq_rg
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingMass_power] with β hβ
      simpa using hβ)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem halfThirdScalingClosedBall_bridge_from_massPowerLaw_on_Ioo :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    1
    (by norm_num : (0 : ℝ) < 1)
    (by
      intro β _hβ
      norm_num [halfThirdScalingMassPrefactor])
    halfThirdScalingMassPrefactor_log_negligible
    (by
      intro β _hβ
      rw [halfThirdScalingClosedBall_predictedExponent_eq_rg]
      simp [halfThirdScalingMass, halfThirdScalingMassPrefactor])
    (by
      intro β _hβ
      unfold halfThirdScalingCorrelationLength halfThirdScalingMass
      rw [show
          -halfThirdScalingRGCertificate.predictedExponent *
              Real.log (halfThirdScalingModel.betaC - β) =
            -(halfThirdScalingRGCertificate.predictedExponent *
              Real.log (halfThirdScalingModel.betaC - β)) by
          ring,
        Real.exp_neg])



theorem halfThirdScalingClosedBall_bridge_from_powerLaw_on_Ioo_congr_pred :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  (halfThirdScalingUnitClosedBallRGPackage.certificate
    halfThirdScalingBlockScale halfThirdScalingModel)
    |>.rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent
      halfThirdScalingRGCertificate
      halfThirdScalingCorrelationLength
      1
      halfThirdScalingClosedBall_predictedExponent_eq_rg
      (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        simp [halfThirdScalingCorrelationLength])



theorem
    halfThirdScalingClosedBall_bridge_from_variablePowerLaw_on_Ioo_congr_pred :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  (halfThirdScalingUnitClosedBallRGPackage.certificate
    halfThirdScalingBlockScale halfThirdScalingModel)
    |>.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
      halfThirdScalingRGCertificate
      halfThirdScalingCorrelationLength
      halfThirdScalingPrefactor
      1
      halfThirdScalingClosedBall_predictedExponent_eq_rg
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num [halfThirdScalingPrefactor])
      halfThirdScalingPrefactor_log_negligible
      (by
        intro β _hβ
        simp [halfThirdScalingCorrelationLength, halfThirdScalingPrefactor])



theorem halfThirdScalingClosedBall_bridge_from_massPowerLaw_on_Ioo_congr_pred :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  (halfThirdScalingUnitClosedBallRGPackage.certificate
    halfThirdScalingBlockScale halfThirdScalingModel)
    |>.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
      halfThirdScalingRGCertificate
      halfThirdScalingCorrelationLength
      halfThirdScalingMass
      halfThirdScalingMassPrefactor
      1
      halfThirdScalingClosedBall_predictedExponent_eq_rg
      (by norm_num : (0 : ℝ) < 1)
      (by
        intro β _hβ
        norm_num [halfThirdScalingMassPrefactor])
      halfThirdScalingMassPrefactor_log_negligible
      (by
        intro β _hβ
        simp [halfThirdScalingMass, halfThirdScalingMassPrefactor])
      (by
        intro β _hβ
        unfold halfThirdScalingCorrelationLength halfThirdScalingMass
        rw [show
            -halfThirdScalingRGCertificate.predictedExponent *
                Real.log (halfThirdScalingModel.betaC - β) =
              -(halfThirdScalingRGCertificate.predictedExponent *
                Real.log (halfThirdScalingModel.betaC - β)) by
            ring,
          Real.exp_neg])



theorem halfThirdScalingClosedBall_valid_from_massPowerLaw_congr_pred :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingCorrelationLength :=
  certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingClosedBall_predictedExponent_eq_rg
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingMass_power] with β hβ
      simpa using hβ)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem halfThirdScalingClosedBall_hasCriticalNu_from_massPowerLaw_congr_pred :
    HasCriticalNu halfThirdScalingModel
      halfThirdScalingCorrelationLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent :=
  certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingClosedBall_predictedExponent_eq_rg
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingMass_power] with β hβ
      simpa using hβ)
    halfThirdScalingCorrelationLength_eq_inv_mass

end ClosedBallExamples



theorem zeroTableClosedBallRGPackage_predictedExponent_eq_rg :
    (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent =
      halfThirdScalingRGCertificate.predictedExponent := by
  rw [zeroTableClosedBallRGPackage_predictedExponent_eq]
  rw [halfThirdScalingRGCertificate_predictedExponent_eq]
  simp [predictedNu, BlockScale.toReal, exampleScale, halfThirdScalingBlockScale]



theorem generatedReplacedTCBRGPackage_predictedExponent_eq_rg :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).predictedExponent =
      halfThirdScalingRGCertificate.predictedExponent := by
  rw [generatedStableKeyReplacedTableClosedBallRGPackage_predictedExponent_eq]
  rw [halfThirdScalingRGCertificate_predictedExponent_eq]
  simp [predictedNu, BlockScale.toReal, exampleScale, halfThirdScalingBlockScale]



theorem genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).predictedExponent =
      halfThirdScalingRGCertificate.predictedExponent := by
  rw [genMinCubicKeyReplacedTableClosedBallRGPackage_predictedExponent_eq]
  rw [halfThirdScalingRGCertificate_predictedExponent_eq]
  simp [predictedNu, BlockScale.toReal, exampleScale, halfThirdScalingBlockScale]



theorem genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg :
    (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent =
      halfThirdScalingRGCertificate.predictedExponent := by
  rw [genBoundedCaseReplacedPackage_predictedExponent_eq]
  rw [halfThirdScalingRGCertificate_predictedExponent_eq]
  simp [predictedNu, BlockScale.toReal, exampleScale, halfThirdScalingBlockScale]



theorem genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg :
    (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent =
      halfThirdScalingRGCertificate.predictedExponent := by
  rw [genCubicClassReplacedPackage_predictedExponent_eq]
  rw [halfThirdScalingRGCertificate_predictedExponent_eq]
  simp [predictedNu, BlockScale.toReal, exampleScale, halfThirdScalingBlockScale]



theorem zeroTableClosedBallRGPackage_closedBallRadius_nonneg :
    0 ≤ zeroTableClosedBallRGPackage.closedBallRadius :=
  zeroTableClosedBallRGPackage.closedBallRadius_nonneg



theorem zeroTableClosedBallRGPackage_closedBallResidual_bound :
    (zeroTableClosedBallRGPackage.closedBallContraction.map
        zeroTableClosedBallRGPackage.closedBallCenter).dist
      zeroTableClosedBallRGPackage.closedBallCenter ≤
        zeroTableClosedBallRGPackage.closedBallResidual :=
  zeroTableClosedBallRGPackage.closedBallResidual_bound



theorem generatedReplacedTCBRGPackage_mapsClosedBall :
    FinitePlusTailState.MapsClosedBall
      generatedStableKeyReplacedTableClosedBallRGPackage.closedBallContraction.map
      generatedStableKeyReplacedTableClosedBallRGPackage.closedBallCenter
      generatedStableKeyReplacedTableClosedBallRGPackage.closedBallRadius :=
  generatedStableKeyReplacedTableClosedBallRGPackage.mapsClosedBall



theorem generatedReplacedTCBRGPackage_closedBall_fixedPoint_isFixed :
    generatedStableKeyReplacedTableClosedBallRGPackage.closedBallContraction.map
        generatedStableKeyReplacedTableClosedBallRGPackage.closedBallRG.closedBall.fixedPoint =
      generatedStableKeyReplacedTableClosedBallRGPackage.closedBallRG.closedBall.fixedPoint :=
  generatedStableKeyReplacedTableClosedBallRGPackage.closedBall_fixedPoint_isFixed



theorem genMinCubicKeyReplacedTCBRGPackage_mapsClosedBall :
    FinitePlusTailState.MapsClosedBall
      genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallContraction.map
      genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallCenter
      genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallRadius :=
  genMinCubicKeyReplacedTableClosedBallRGPackage.mapsClosedBall



theorem genMinCubicKeyReplacedTCBRGPackage_closedBall_fixedPoint_isFixed :
    let fp :=
      genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallRG.closedBall.fixedPoint
    genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallContraction.map fp =
      fp := by
  dsimp
  exact genMinCubicKeyReplacedTableClosedBallRGPackage.closedBall_fixedPoint_isFixed



theorem genBoundedCaseReplacedTCBRGPackage_mapsClosedBall :
    FinitePlusTailState.MapsClosedBall
      genBoundedCaseReplacedPackage.closedBallContraction.map
      genBoundedCaseReplacedPackage.closedBallCenter
      genBoundedCaseReplacedPackage.closedBallRadius :=
  genBoundedCaseReplacedPackage.mapsClosedBall



theorem genBoundedCaseReplacedTCBRGPackage_closedBall_fixedPoint_isFixed :
    genBoundedCaseReplacedPackage.closedBallContraction.map
        genBoundedCaseReplacedPackage.closedBallRG.closedBall.fixedPoint =
      genBoundedCaseReplacedPackage.closedBallRG.closedBall.fixedPoint :=
  genBoundedCaseReplacedPackage.closedBall_fixedPoint_isFixed



theorem genCubicClassReplacedTCBRGPackage_mapsClosedBall :
    FinitePlusTailState.MapsClosedBall
      genCubicClassReplacedPackage.closedBallContraction.map
      genCubicClassReplacedPackage.closedBallCenter
      genCubicClassReplacedPackage.closedBallRadius :=
  genCubicClassReplacedPackage.mapsClosedBall



theorem genCubicClassReplacedTCBRGPackage_closedBall_fixedPoint_isFixed :
    genCubicClassReplacedPackage.closedBallContraction.map
        genCubicClassReplacedPackage.closedBallRG.closedBall.fixedPoint =
      genCubicClassReplacedPackage.closedBallRG.closedBall.fixedPoint :=
  genCubicClassReplacedPackage.closedBall_fixedPoint_isFixed



theorem zeroTableClosedBallRGPackage_bridge_from_powerLaw_wrapper :
    (zeroTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_power_prefactor
    zeroTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [halfThirdScalingCorrelationLength_exact_power] with β hβ
      simpa [zeroTableClosedBallRGPackage_predictedExponent_eq_rg] using hβ)



theorem generatedReplacedTCBRGPackage_bridge_from_powerLaw_wrapper :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_power_prefactor
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [halfThirdScalingCorrelationLength_exact_power] with β hβ
      simpa [generatedReplacedTCBRGPackage_predictedExponent_eq_rg] using hβ)



theorem genMinCubicKeyReplacedTCBRGPackage_bridge_from_powerLaw_wrapper :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_power_prefactor
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [halfThirdScalingCorrelationLength_exact_power] with β hβ
      simpa [genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)



theorem genBoundedCaseReplacedTCBRGPackage_bridge_from_powerLaw_wrapper :
    (genBoundedCaseReplacedPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_power_prefactor
    genBoundedCaseReplacedPackage
    exampleScale
    halfThirdScalingCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [halfThirdScalingCorrelationLength_exact_power] with β hβ
      simpa [genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)



theorem genCubicClassReplacedTCBRGPackage_bridge_from_powerLaw_wrapper :
    (genCubicClassReplacedPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_power_prefactor
    genCubicClassReplacedPackage
    exampleScale
    halfThirdScalingCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [halfThirdScalingCorrelationLength_exact_power] with β hβ
      simpa [genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)



theorem generatedReplacedTCBRGPackage_bridge_from_variablePowerLaw_wrapper :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingCorrelationLength_prefactor_power]
        with β hβ
      simpa [generatedReplacedTCBRGPackage_predictedExponent_eq_rg] using hβ)



theorem
    genMinCubicKeyReplacedTCBRGPackage_bridge_from_variablePowerLaw_wrapper :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingCorrelationLength_prefactor_power]
        with β hβ
      simpa [genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)



theorem genBoundedCaseReplacedTCBRGPackage_bridge_from_variablePowerLaw_wrapper :
    (genBoundedCaseReplacedPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor
    genBoundedCaseReplacedPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingCorrelationLength_prefactor_power]
        with β hβ
      simpa [genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)



theorem
    genCubicClassReplacedTCBRGPackage_bridge_from_variablePowerLaw_wrapper :
    (genCubicClassReplacedPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor
    genCubicClassReplacedPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingCorrelationLength_prefactor_power]
        with β hβ
      simpa [genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)



theorem generatedReplacedTCBRGPackage_bridge_from_massPowerLaw_wrapper :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingMass_power] with β hβ
      simpa [generatedReplacedTCBRGPackage_predictedExponent_eq_rg] using hβ)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem genMinCubicKeyReplacedTCBRGPackage_bridge_from_massPowerLaw_wrapper :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingMass_power] with β hβ
      simpa [genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem genBoundedCaseReplacedTCBRGPackage_bridge_from_massPowerLaw_wrapper :
    (genBoundedCaseReplacedPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
    genBoundedCaseReplacedPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingMass_power] with β hβ
      simpa [genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem genCubicClassReplacedTCBRGPackage_bridge_from_massPowerLaw_wrapper :
    (genCubicClassReplacedPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
    genCubicClassReplacedPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingMass_power] with β hβ
      simpa [genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem zeroTableClosedBallRGPackage_bridge_from_variablePowerLaw_wrapper :
    (zeroTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor
    zeroTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingCorrelationLength_prefactor_power]
        with β hβ
      simpa [zeroTableClosedBallRGPackage_predictedExponent_eq_rg] using hβ)



theorem zeroTableClosedBallRGPackage_bridge_from_massPowerLaw_wrapper :
    (zeroTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
    zeroTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingMass_power] with β hβ
      simpa [zeroTableClosedBallRGPackage_predictedExponent_eq_rg] using hβ)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem zeroTableClosedBallRGPackage_valid_from_powerLaw_wrapper :
    (zeroTableClosedBallRGPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  InfiniteTailTableClosedBallRGPackage.certificate_valid_of_eventually_exact_power_prefactor
    zeroTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [halfThirdScalingCorrelationLength_exact_power] with β hβ
      simpa [zeroTableClosedBallRGPackage_predictedExponent_eq_rg] using hβ)



theorem zeroTableClosedBallRGPackage_hasCriticalNu_from_powerLaw_wrapper :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent :=
  InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_exact_power_prefactor
    zeroTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [halfThirdScalingCorrelationLength_exact_power] with β hβ
      simpa [zeroTableClosedBallRGPackage_predictedExponent_eq_rg] using hβ)



theorem generatedReplacedTCBRGPackage_valid_from_powerLaw_wrapper :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid halfThirdScalingCorrelationLength :=
  InfiniteTailTableClosedBallRGPackage.certificate_valid_of_eventually_exact_power_prefactor
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [halfThirdScalingCorrelationLength_exact_power] with β hβ
      simpa [generatedReplacedTCBRGPackage_predictedExponent_eq_rg] using hβ)



theorem generatedReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_wrapper :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent :=
  InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_exact_power_prefactor
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [halfThirdScalingCorrelationLength_exact_power] with β hβ
      simpa [generatedReplacedTCBRGPackage_predictedExponent_eq_rg] using hβ)



theorem genMinCubicKeyReplacedTCBRGPackage_valid_from_powerLaw_wrapper :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid halfThirdScalingCorrelationLength :=
  InfiniteTailTableClosedBallRGPackage.certificate_valid_of_eventually_exact_power_prefactor
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [halfThirdScalingCorrelationLength_exact_power] with β hβ
      simpa [genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)



theorem genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_wrapper :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent :=
  InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_exact_power_prefactor
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [halfThirdScalingCorrelationLength_exact_power] with β hβ
      simpa [genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)



theorem genBoundedCaseReplacedTCBRGPackage_valid_from_powerLaw_wrapper :
    (genBoundedCaseReplacedPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  InfiniteTailTableClosedBallRGPackage.certificate_valid_of_eventually_exact_power_prefactor
    genBoundedCaseReplacedPackage
    exampleScale
    halfThirdScalingCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [halfThirdScalingCorrelationLength_exact_power] with β hβ
      simpa [genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)



theorem genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_wrapper :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent :=
  InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_exact_power_prefactor
    genBoundedCaseReplacedPackage
    exampleScale
    halfThirdScalingCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [halfThirdScalingCorrelationLength_exact_power] with β hβ
      simpa [genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)



theorem genCubicClassReplacedTCBRGPackage_valid_from_powerLaw_wrapper :
    (genCubicClassReplacedPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  InfiniteTailTableClosedBallRGPackage.certificate_valid_of_eventually_exact_power_prefactor
    genCubicClassReplacedPackage
    exampleScale
    halfThirdScalingCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [halfThirdScalingCorrelationLength_exact_power] with β hβ
      simpa [genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)



theorem genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_wrapper :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent :=
  InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_exact_power_prefactor
    genCubicClassReplacedPackage
    exampleScale
    halfThirdScalingCorrelationLength
    (by norm_num : (0 : ℝ) < 1)
    (by
      filter_upwards [halfThirdScalingCorrelationLength_exact_power] with β hβ
      simpa [genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)



theorem generatedReplacedTCBRGPackage_valid_from_variablePowerLaw_wrapper :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_power_variable_prefactor
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingCorrelationLength_prefactor_power]
        with β hβ
      simpa [generatedReplacedTCBRGPackage_predictedExponent_eq_rg] using hβ)



theorem
    generatedReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_wrapper :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingCorrelationLength_prefactor_power]
        with β hβ
      simpa [generatedReplacedTCBRGPackage_predictedExponent_eq_rg] using hβ)



theorem generatedReplacedTCBRGPackage_valid_from_massPowerLaw_wrapper :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_mass_power_variable_prefactor
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingMass_power] with β hβ
      simpa [generatedReplacedTCBRGPackage_predictedExponent_eq_rg] using hβ)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem generatedReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_wrapper :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingMass_power] with β hβ
      simpa [generatedReplacedTCBRGPackage_predictedExponent_eq_rg] using hβ)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem
    genMinCubicKeyReplacedTCBRGPackage_valid_from_variablePowerLaw_wrapper :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_power_variable_prefactor
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingCorrelationLength_prefactor_power]
        with β hβ
      simpa [genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)



theorem
    genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_wrapper :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingCorrelationLength_prefactor_power]
        with β hβ
      simpa [genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)



theorem genMinCubicKeyReplacedTCBRGPackage_valid_from_massPowerLaw_wrapper :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_mass_power_variable_prefactor
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingMass_power] with β hβ
      simpa [genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_wrapper :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingMass_power] with β hβ
      simpa [genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)
    halfThirdScalingCorrelationLength_eq_inv_mass




theorem genBoundedCaseReplacedTCBRGPackage_valid_from_variablePowerLaw_wrapper :
    (genBoundedCaseReplacedPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_power_variable_prefactor
    genBoundedCaseReplacedPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingCorrelationLength_prefactor_power]
        with β hβ
      simpa [genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)



theorem
    genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_wrapper :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor
    genBoundedCaseReplacedPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingCorrelationLength_prefactor_power]
        with β hβ
      simpa [genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)



theorem genBoundedCaseReplacedTCBRGPackage_valid_from_massPowerLaw_wrapper :
    (genBoundedCaseReplacedPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_mass_power_variable_prefactor
    genBoundedCaseReplacedPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingMass_power] with β hβ
      simpa [genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_wrapper :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor
    genBoundedCaseReplacedPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingMass_power] with β hβ
      simpa [genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem
    genCubicClassReplacedTCBRGPackage_valid_from_variablePowerLaw_wrapper :
    (genCubicClassReplacedPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_power_variable_prefactor
    genCubicClassReplacedPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingCorrelationLength_prefactor_power]
        with β hβ
      simpa [genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)



theorem
    genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_wrapper :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor
    genCubicClassReplacedPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingCorrelationLength_prefactor_power]
        with β hβ
      simpa [genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)



theorem genCubicClassReplacedTCBRGPackage_valid_from_massPowerLaw_wrapper :
    (genCubicClassReplacedPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_mass_power_variable_prefactor
    genCubicClassReplacedPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingMass_power] with β hβ
      simpa [genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_wrapper :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor
    genCubicClassReplacedPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingMass_power] with β hβ
      simpa [genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg]
        using hβ)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem zeroTableClosedBallRGPackage_valid_from_variablePowerLaw_wrapper :
    (zeroTableClosedBallRGPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_power_variable_prefactor
    zeroTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingCorrelationLength_prefactor_power]
        with β hβ
      simpa [zeroTableClosedBallRGPackage_predictedExponent_eq_rg] using hβ)



theorem zeroTableClosedBallRGPackage_hasCriticalNu_from_variablePowerLaw_wrapper :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor
    zeroTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingCorrelationLength_prefactor_power]
        with β hβ
      simpa [zeroTableClosedBallRGPackage_predictedExponent_eq_rg] using hβ)



theorem zeroTableClosedBallRGPackage_valid_from_massPowerLaw_wrapper :
    (zeroTableClosedBallRGPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_mass_power_variable_prefactor
    zeroTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingMass_power] with β hβ
      simpa [zeroTableClosedBallRGPackage_predictedExponent_eq_rg] using hβ)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem zeroTableClosedBallRGPackage_hasCriticalNu_from_massPowerLaw_wrapper :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor
    zeroTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      filter_upwards [halfThirdScalingMass_power] with β hβ
      simpa [zeroTableClosedBallRGPackage_predictedExponent_eq_rg] using hβ)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem zeroTableClosedBallRGPackage_bridge_from_powerLaw_on_Ioo :
    (zeroTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo
    zeroTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    1
    (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1)
    (by
      intro β _hβ
      rw [zeroTableClosedBallRGPackage_predictedExponent_eq_rg]
      simp [halfThirdScalingCorrelationLength, halfThirdScalingModel,
        ToyCriticalModel])



theorem zeroTableClosedBallRGPackage_bridge_from_variablePowerLaw_on_Ioo :
    (zeroTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo
    zeroTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    1
    (by norm_num : (0 : ℝ) < 1)
    (by
      intro β _hβ
      norm_num [halfThirdScalingPrefactor])
    halfThirdScalingPrefactor_log_negligible
    (by
      intro β _hβ
      rw [zeroTableClosedBallRGPackage_predictedExponent_eq_rg]
      simp [halfThirdScalingCorrelationLength, halfThirdScalingPrefactor,
        halfThirdScalingModel, ToyCriticalModel])



theorem zeroTableClosedBallRGPackage_bridge_from_massPowerLaw_on_Ioo :
    (zeroTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
    zeroTableClosedBallRGPackage
    exampleScale
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    1
    (by norm_num : (0 : ℝ) < 1)
    (by
      intro β _hβ
      norm_num [halfThirdScalingMassPrefactor])
    halfThirdScalingMassPrefactor_log_negligible
    (by
      intro β _hβ
      rw [zeroTableClosedBallRGPackage_predictedExponent_eq_rg]
      simp [halfThirdScalingMass, halfThirdScalingMassPrefactor,
        halfThirdScalingModel, ToyCriticalModel])
    (by
      intro β _hβ
      unfold halfThirdScalingCorrelationLength halfThirdScalingMass
      rw [show
          -halfThirdScalingRGCertificate.predictedExponent *
              Real.log (halfThirdScalingModel.betaC - β) =
            -(halfThirdScalingRGCertificate.predictedExponent *
              Real.log (halfThirdScalingModel.betaC - β)) by
          ring,
        Real.exp_neg])



theorem zeroTableClosedBallRGPackage_bridge_from_powerLaw_on_Ioo_congr_pred :
    (zeroTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_pred
    zeroTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    1
    (by simpa using zeroTableClosedBallRGPackage_predictedExponent_eq_rg)
    (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1)
    (by
      intro β _hβ
      simp [halfThirdScalingCorrelationLength, halfThirdScalingModel,
        ToyCriticalModel])




theorem
    zeroTableClosedBallRGPackage_bridge_from_variablePowerLaw_on_Ioo_congr_pred :
    (zeroTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred
    zeroTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    1
    (by simpa using zeroTableClosedBallRGPackage_predictedExponent_eq_rg)
    (by norm_num : (0 : ℝ) < 1)
    (by
      intro β _hβ
      norm_num [halfThirdScalingPrefactor])
    halfThirdScalingPrefactor_log_negligible
    (by
      intro β _hβ
      simp [halfThirdScalingCorrelationLength, halfThirdScalingPrefactor,
        halfThirdScalingModel, ToyCriticalModel])



theorem zeroTableClosedBallRGPackage_bridge_from_massPowerLaw_on_Ioo_congr_pred :
    (zeroTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred
    zeroTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    1
    (by simpa using zeroTableClosedBallRGPackage_predictedExponent_eq_rg)
    (by norm_num : (0 : ℝ) < 1)
    (by
      intro β _hβ
      norm_num [halfThirdScalingMassPrefactor])
    halfThirdScalingMassPrefactor_log_negligible
    (by
      intro β _hβ
      simp [halfThirdScalingMass, halfThirdScalingMassPrefactor,
        halfThirdScalingModel, ToyCriticalModel])
    (by
      intro β _hβ
      unfold halfThirdScalingCorrelationLength halfThirdScalingMass
      rw [show
          -halfThirdScalingRGCertificate.predictedExponent *
              Real.log (halfThirdScalingModel.betaC - β) =
            -(halfThirdScalingRGCertificate.predictedExponent *
              Real.log (halfThirdScalingModel.betaC - β)) by
          ring,
        Real.exp_neg])



theorem zeroTableClosedBallRGPackage_bridge_from_powerLaw_congr_pred :
    (zeroTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_pred
    zeroTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    (by simpa using zeroTableClosedBallRGPackage_predictedExponent_eq_rg)
    (by norm_num : (0 : ℝ) < 1)
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_exact_power)



theorem generatedReplacedTCBRGPackage_bridge_from_powerLaw_congr_pred :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_pred
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    (by simpa using generatedReplacedTCBRGPackage_predictedExponent_eq_rg)
    (by norm_num : (0 : ℝ) < 1)
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_exact_power)



theorem genMinCubicKeyReplacedTCBRGPackage_bridge_from_powerLaw_congr_pred :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_pred
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    (by simpa using genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg)
    (by norm_num : (0 : ℝ) < 1)
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_exact_power)



theorem genBoundedCaseReplacedTCBRGPackage_bridge_from_powerLaw_congr_pred :
    (genBoundedCaseReplacedPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_pred
    genBoundedCaseReplacedPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    (by simpa using genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg)
    (by norm_num : (0 : ℝ) < 1)
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_exact_power)



theorem genCubicClassReplacedTCBRGPackage_bridge_from_powerLaw_congr_pred :
    (genCubicClassReplacedPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_pred
    genCubicClassReplacedPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    (by simpa using genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg)
    (by norm_num : (0 : ℝ) < 1)
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_exact_power)



theorem zeroTableClosedBallRGPackage_bridge_from_variablePowerLaw_congr_pred :
    (zeroTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred
    zeroTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    (by simpa using zeroTableClosedBallRGPackage_predictedExponent_eq_rg)
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_prefactor_power)




theorem
    generatedReplacedTCBRGPackage_bridge_from_variablePowerLaw_congr_pred :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    (by simpa using generatedReplacedTCBRGPackage_predictedExponent_eq_rg)
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_prefactor_power)




theorem
    genMinCubicKeyReplacedTCBRGPackage_bridge_from_variablePowerLaw_congr_pred :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    (by simpa using genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg)
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_prefactor_power)




theorem
    genBoundedCaseReplacedTCBRGPackage_bridge_from_variablePowerLaw_congr_pred :
    (genBoundedCaseReplacedPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred
    genBoundedCaseReplacedPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    (by simpa using genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg)
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_prefactor_power)




theorem
    genCubicClassReplacedTCBRGPackage_bridge_from_variablePowerLaw_congr_pred :
    (genCubicClassReplacedPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred
    genCubicClassReplacedPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    (by simpa using genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg)
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_prefactor_power)



theorem zeroTableClosedBallRGPackage_bridge_from_massPowerLaw_congr_pred :
    (zeroTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    zeroTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    (by simpa using zeroTableClosedBallRGPackage_predictedExponent_eq_rg)
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingMass_power)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem generatedReplacedTCBRGPackage_bridge_from_massPowerLaw_congr_pred :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    (by simpa using generatedReplacedTCBRGPackage_predictedExponent_eq_rg)
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingMass_power)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem genMinCubicKeyReplacedTCBRGPackage_bridge_from_massPowerLaw_congr_pred :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    (by simpa using genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg)
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingMass_power)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem genBoundedCaseReplacedTCBRGPackage_bridge_from_massPowerLaw_congr_pred :
    (genBoundedCaseReplacedPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    genBoundedCaseReplacedPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    (by simpa using genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg)
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingMass_power)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem genCubicClassReplacedTCBRGPackage_bridge_from_massPowerLaw_congr_pred :
    (genCubicClassReplacedPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    genCubicClassReplacedPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    (by simpa using genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg)
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingMass_power)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem zeroTableClosedBallRGPackage_valid_from_powerLaw_congr_pred :
    (zeroTableClosedBallRGPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_power_prefactor_congr_pred
    zeroTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    (by simpa using zeroTableClosedBallRGPackage_predictedExponent_eq_rg)
    (by norm_num : (0 : ℝ) < 1)
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_exact_power)



theorem zeroTableClosedBallRGPackage_hasCriticalNu_from_powerLaw_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_power_prefactor_congr_pred
    zeroTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    (by simpa using zeroTableClosedBallRGPackage_predictedExponent_eq_rg)
    (by norm_num : (0 : ℝ) < 1)
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_exact_power)



theorem zeroTableClosedBallRGPackage_valid_from_variablePowerLaw_congr_pred :
    (zeroTableClosedBallRGPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_power_variable_prefactor_congr_pred
    zeroTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    (by simpa using zeroTableClosedBallRGPackage_predictedExponent_eq_rg)
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_prefactor_power)



theorem zeroTableClosedBallRGPackage_hasCriticalNu_from_variablePowerLaw_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_pred
    zeroTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    (by simpa using zeroTableClosedBallRGPackage_predictedExponent_eq_rg)
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_prefactor_power)



theorem zeroTableClosedBallRGPackage_valid_from_massPowerLaw_congr_pred :
    (zeroTableClosedBallRGPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    zeroTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    (by simpa using zeroTableClosedBallRGPackage_predictedExponent_eq_rg)
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingMass_power)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem zeroTableClosedBallRGPackage_hasCriticalNu_from_massPowerLaw_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    zeroTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    (by simpa using zeroTableClosedBallRGPackage_predictedExponent_eq_rg)
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingMass_power)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem generatedReplacedTCBRGPackage_valid_from_powerLaw_congr_pred :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_power_prefactor_congr_pred
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    (by simpa using generatedReplacedTCBRGPackage_predictedExponent_eq_rg)
    (by norm_num : (0 : ℝ) < 1)
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_exact_power)



theorem generatedReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_power_prefactor_congr_pred
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    (by simpa using generatedReplacedTCBRGPackage_predictedExponent_eq_rg)
    (by norm_num : (0 : ℝ) < 1)
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_exact_power)



theorem generatedReplacedTCBRGPackage_valid_from_variablePowerLaw_congr_pred :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_power_variable_prefactor_congr_pred
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    (by simpa using generatedReplacedTCBRGPackage_predictedExponent_eq_rg)
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_prefactor_power)



theorem
    generatedReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_pred
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    (by simpa using generatedReplacedTCBRGPackage_predictedExponent_eq_rg)
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_prefactor_power)



theorem generatedReplacedTCBRGPackage_valid_from_massPowerLaw_congr_pred :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    (by simpa using generatedReplacedTCBRGPackage_predictedExponent_eq_rg)
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingMass_power)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem generatedReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    (by simpa using generatedReplacedTCBRGPackage_predictedExponent_eq_rg)
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingMass_power)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem genMinCubicKeyReplacedTCBRGPackage_valid_from_powerLaw_congr_pred :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_power_prefactor_congr_pred
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    (by simpa using genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg)
    (by norm_num : (0 : ℝ) < 1)
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_exact_power)



theorem genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_power_prefactor_congr_pred
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    (by simpa using genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg)
    (by norm_num : (0 : ℝ) < 1)
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_exact_power)




theorem
    genMinCubicKeyReplacedTCBRGPackage_valid_from_variablePowerLaw_congr_pred :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_power_variable_prefactor_congr_pred
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    (by simpa using genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg)
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_prefactor_power)



theorem
    genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_pred
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    (by simpa using genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg)
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_prefactor_power)



theorem genMinCubicKeyReplacedTCBRGPackage_valid_from_massPowerLaw_congr_pred :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    (by simpa using genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg)
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingMass_power)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem
    genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    (by simpa using genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg)
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingMass_power)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem genBoundedCaseReplacedTCBRGPackage_valid_from_powerLaw_congr_pred :
    (genBoundedCaseReplacedPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_power_prefactor_congr_pred
    genBoundedCaseReplacedPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    (by simpa using genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg)
    (by norm_num : (0 : ℝ) < 1)
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_exact_power)



theorem genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_power_prefactor_congr_pred
    genBoundedCaseReplacedPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    (by simpa using genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg)
    (by norm_num : (0 : ℝ) < 1)
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_exact_power)




theorem
    genBoundedCaseReplacedTCBRGPackage_valid_from_variablePowerLaw_congr_pred :
    (genBoundedCaseReplacedPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_power_variable_prefactor_congr_pred
    genBoundedCaseReplacedPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    (by simpa using genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg)
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_prefactor_power)



theorem
    genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_pred
    genBoundedCaseReplacedPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    (by simpa using genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg)
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_prefactor_power)



theorem genBoundedCaseReplacedTCBRGPackage_valid_from_massPowerLaw_congr_pred :
    (genBoundedCaseReplacedPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    genBoundedCaseReplacedPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    (by simpa using genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg)
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingMass_power)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem
    genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    genBoundedCaseReplacedPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    (by simpa using genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg)
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingMass_power)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem genCubicClassReplacedTCBRGPackage_valid_from_powerLaw_congr_pred :
    (genCubicClassReplacedPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_power_prefactor_congr_pred
    genCubicClassReplacedPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    (by simpa using genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg)
    (by norm_num : (0 : ℝ) < 1)
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_exact_power)



theorem genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_power_prefactor_congr_pred
    genCubicClassReplacedPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    (by simpa using genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg)
    (by norm_num : (0 : ℝ) < 1)
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_exact_power)




theorem
    genCubicClassReplacedTCBRGPackage_valid_from_variablePowerLaw_congr_pred :
    (genCubicClassReplacedPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_power_variable_prefactor_congr_pred
    genCubicClassReplacedPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    (by simpa using genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg)
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_prefactor_power)



theorem
    genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_pred
    genCubicClassReplacedPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingPrefactor
    (by simpa using genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg)
    halfThirdScalingPrefactor_pos
    halfThirdScalingPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingCorrelationLength_prefactor_power)



theorem genCubicClassReplacedTCBRGPackage_valid_from_massPowerLaw_congr_pred :
    (genCubicClassReplacedPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    genCubicClassReplacedPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    (by simpa using genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg)
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingMass_power)
    halfThirdScalingCorrelationLength_eq_inv_mass



theorem
    genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent :=
  open InfiniteTailTableClosedBallRGPackage in
  certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred
    genCubicClassReplacedPackage
    exampleScale
    (halfThirdScalingRGCertificate.retarget
      (ToyCriticalModel exampleScale 3))
    halfThirdScalingCorrelationLength
    halfThirdScalingMass
    halfThirdScalingMassPrefactor
    (by simpa using genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg)
    halfThirdScalingMassPrefactor_pos
    halfThirdScalingMassPrefactor_log_negligible
    (by
      simpa [halfThirdScalingModel, ToyCriticalModel] using
        halfThirdScalingMass_power)
    halfThirdScalingCorrelationLength_eq_inv_mass

end PackagePowerLawBridgeExample
end Exact3D
end StatMech

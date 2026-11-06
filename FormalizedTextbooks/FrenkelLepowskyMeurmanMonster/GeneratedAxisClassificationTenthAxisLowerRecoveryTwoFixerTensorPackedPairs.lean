/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerTensorCircuitActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryJointPackedPair00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryJointPackedPair01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryJointPackedPair02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryJointPackedPair03SourceCorrected
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryJointPackedPair04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedCandidate10Pair00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedCandidate10Pair01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedCandidate10Pair02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedCandidate10Pair03SourceCorrected

/-! Ungated exact two-fixer full tensor circuit assembly. All source bindings remain explicit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- All nine complete original packed pair certificates imply the full two-fixer pair interface. -/
theorem generatedTenth_two_fixer_tensor_packed_pairs : GeneratedTenthTwoFixerTensorPairCondition :=
  by
  intro g j s p hp n
  fin_cases g
  · rcases s with _ | (_ | (_ | (_ | (_ | s))))
    · change some ((0 : Fin 12), (1 : Fin 12)) = some p at hp
      have hpair := Option.some.inj hp
      subst p
      change generatedNinthLowerSpinTensorFourierInteger 0
        (generatedNinthLowerSpinTensorFourierInteger 1
          (generatedNinthLowerSpinTensorPackedCoordinate
            (generatedTenthAxisLowerRecoveryJointPackedStage00Words j))) n =
            2 * generatedNinthLowerSpinTensorPackedCoordinate
              (generatedTenthAxisLowerRecoveryJointPackedStage01Words j) n
      exact generatedTenth_axis_lower_recovery_joint_packed_pair00_actual_fourier j n
    · change some ((2 : Fin 12), (3 : Fin 12)) = some p at hp
      have hpair := Option.some.inj hp
      subst p
      change generatedNinthLowerSpinTensorFourierInteger 2
        (generatedNinthLowerSpinTensorFourierInteger 3
          (generatedNinthLowerSpinTensorPackedCoordinate
            (generatedTenthAxisLowerRecoveryJointPackedStage01Words j))) n =
            2 * generatedNinthLowerSpinTensorPackedCoordinate
              (generatedTenthAxisLowerRecoveryJointPackedStage02Words j) n
      exact generatedTenth_axis_lower_recovery_joint_packed_pair01_actual_fourier j n
    · change some ((4 : Fin 12), (5 : Fin 12)) = some p at hp
      have hpair := Option.some.inj hp
      subst p
      change generatedNinthLowerSpinTensorFourierInteger 4
        (generatedNinthLowerSpinTensorFourierInteger 5
          (generatedNinthLowerSpinTensorPackedCoordinate
            (generatedTenthAxisLowerRecoveryJointPackedStage02Words j))) n =
            2 * generatedNinthLowerSpinTensorPackedCoordinate
              (generatedTenthAxisLowerRecoveryJointPackedStage03Words j) n
      exact generatedTenth_axis_lower_recovery_joint_packed_pair02_actual_fourier j n
    · change some ((6 : Fin 12), (7 : Fin 12)) = some p at hp
      have hpair := Option.some.inj hp
      subst p
      change generatedNinthLowerSpinTensorFourierInteger 6
        (generatedNinthLowerSpinTensorFourierInteger 7
          (generatedNinthLowerSpinTensorPackedCoordinate
            (generatedTenthAxisLowerRecoveryJointPackedStage03Words j))) n =
            2 * generatedNinthLowerSpinTensorPackedCoordinate
              (generatedTenthAxisLowerRecoveryJointPackedStage04Words j) n
      exact generatedTenth_axis_lower_recovery_joint_packed_pair03_actual_fourier j n
    · change some ((8 : Fin 12), (9 : Fin 12)) = some p at hp
      have hpair := Option.some.inj hp
      subst p
      change generatedNinthLowerSpinTensorFourierInteger 8
        (generatedNinthLowerSpinTensorFourierInteger 9
          (generatedNinthLowerSpinTensorPackedCoordinate
            (generatedTenthAxisLowerRecoveryJointPackedStage04Words j))) n =
            2 * generatedNinthLowerSpinTensorPackedCoordinate
              (generatedTenthAxisLowerRecoveryJointPackedStage05Words j) n
      exact generatedTenth_axis_lower_recovery_joint_packed_pair04_actual_fourier j n
    · change (none : Option (Fin 12 × Fin 12)) = some p at hp
      cases hp
  · rcases s with _ | (_ | (_ | (_ | s)))
    · change some ((0 : Fin 12), (1 : Fin 12)) = some p at hp
      have hpair := Option.some.inj hp
      subst p
      change generatedNinthLowerSpinTensorFourierInteger 0
        (generatedNinthLowerSpinTensorFourierInteger 1
          (generatedNinthLowerSpinTensorPackedCoordinate
            (generatedTenthAxisLowerRecoveryPackedCandidate10Stage00Words j))) n =
            2 * generatedNinthLowerSpinTensorPackedCoordinate
              (generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words j) n
      exact generatedTenth_axis_lower_recovery_packed_candidate10_pair00_actual_fourier j n
    · change some ((2 : Fin 12), (3 : Fin 12)) = some p at hp
      have hpair := Option.some.inj hp
      subst p
      change generatedNinthLowerSpinTensorFourierInteger 2
        (generatedNinthLowerSpinTensorFourierInteger 3
          (generatedNinthLowerSpinTensorPackedCoordinate
            (generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words j))) n =
            2 * generatedNinthLowerSpinTensorPackedCoordinate
              (generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words j) n
      exact generatedTenth_axis_lower_recovery_packed_candidate10_pair01_actual_fourier j n
    · change some ((4 : Fin 12), (5 : Fin 12)) = some p at hp
      have hpair := Option.some.inj hp
      subst p
      change generatedNinthLowerSpinTensorFourierInteger 4
        (generatedNinthLowerSpinTensorFourierInteger 5
          (generatedNinthLowerSpinTensorPackedCoordinate
            (generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words j))) n =
            2 * generatedNinthLowerSpinTensorPackedCoordinate
              (generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words j) n
      exact generatedTenth_axis_lower_recovery_packed_candidate10_pair02_actual_fourier j n
    · change some ((6 : Fin 12), (7 : Fin 12)) = some p at hp
      have hpair := Option.some.inj hp
      subst p
      change generatedNinthLowerSpinTensorFourierInteger 6
        (generatedNinthLowerSpinTensorFourierInteger 7
          (generatedNinthLowerSpinTensorPackedCoordinate
            (generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words j))) n =
            2 * generatedNinthLowerSpinTensorPackedCoordinate
              (generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words j) n
      exact generatedTenth_axis_lower_recovery_packed_candidate10_pair03_actual_fourier j n
    · change (none : Option (Fin 12 × Fin 12)) = some p at hp
      cases hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryJointPackedStage00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryJointPackedStage01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryJointPackedStage02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryJointPackedStage03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryJointPackedStage04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryJointPackedStage05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryJointPackedStage06

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The seven complete signed joint source, Fourier-pair, and final packed stages. -/
def generatedTenthAxisLowerRecoveryJointPackedCache : Fin 7 → Fin 24 → Fin 16 → Fin 16 → ℕ :=
  ![generatedTenthAxisLowerRecoveryJointPackedStage00Words,
    generatedTenthAxisLowerRecoveryJointPackedStage01Words,
    generatedTenthAxisLowerRecoveryJointPackedStage02Words,
    generatedTenthAxisLowerRecoveryJointPackedStage03Words,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
    generatedTenthAxisLowerRecoveryJointPackedStage05Words,
    generatedTenthAxisLowerRecoveryJointPackedStage06Words]

/-- The literal common real denominator retained by the joint-stage packets. -/
def generatedTenthAxisLowerRecoveryJointPackedCacheDenominator : ℕ := 512

/-- The literal joint-stage physical scale; actual tensor binding remains separate. -/
def generatedTenthAxisLowerRecoveryJointPackedCachePhysicalScale : ℕ := 4

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

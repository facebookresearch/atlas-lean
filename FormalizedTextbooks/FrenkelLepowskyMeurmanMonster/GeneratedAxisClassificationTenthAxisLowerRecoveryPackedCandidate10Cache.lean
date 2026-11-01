/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedCandidate10Stage00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedCandidate10Stage01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedCandidate10Stage02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedCandidate10Stage03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedCandidate10Stage04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedCandidate10Stage05

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- All source, paired Fourier and final stages of this exact candidate. -/
def generatedTenthAxisLowerRecoveryPackedCandidate10Cache : Fin 6 → Fin 24 → Fin 16 → Fin 16 → ℕ :=
  ![generatedTenthAxisLowerRecoveryPackedCandidate10Stage00Words,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage05Words]

/-- Every original stage keeps the exact original tensor denominator. -/
def generatedTenthAxisLowerRecoveryPackedCandidate10CacheDenominator : ℕ := 512

/-- The actual spatial numerator is normalized before the compact spin action. -/
def generatedTenthAxisLowerRecoveryPackedCandidate10CachePhysicalScale : ℕ := 4

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactData

/-! Separate complete original Root02 source compact spin data. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Complete original source data, retaining every coordinate. -/
def generatedTenthAxisLowerRecoverySourceCompactLeftColumns : Fin 1 → Fin 12 → ℕ :=
  ![![753, 276, 2333, 315, 1549, 2290, 252, 3947, 1954, 1874, 253, 15]]

/-- Complete original source data, retaining every coordinate. -/
def generatedTenthAxisLowerRecoverySourceCompactLeftInverseColumns : Fin 1 → Fin 12 → ℕ :=
  ![![1088, 3840, 2854, 2150, 2700, 2058, 308, 178, 424, 1857, 81, 3104]]

/-- Complete original source data, retaining every coordinate. -/
def generatedTenthAxisLowerRecoverySourceCompactRightColumns : Fin 1 → Fin 12 → ℕ :=
  ![![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]]

/-- Complete original source data, retaining every coordinate. -/
def generatedTenthAxisLowerRecoverySourceCompactRightInverseColumns : Fin 1 → Fin 12 → ℕ :=
  ![![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]]

/-- Complete original source data, retaining every coordinate. -/
def generatedTenthAxisLowerRecoverySourceCompactFirstPhaseRows : Fin 1 → Fin 12 → ℕ :=
  ![![2184, 772, 1320, 400, 2176, 3200, 0, 1024, 512, 0, 2048, 0]]

/-- Complete original source data, retaining every coordinate. -/
def generatedTenthAxisLowerRecoverySourceCompactSecondPhaseRows : Fin 1 → Fin 12 → ℕ :=
  ![![3072, 512, 256, 3872, 32, 1728, 3584, 3840, 512, 3072, 0, 0]]

/-- Complete original source data, retaining every coordinate. -/
def generatedTenthAxisLowerRecoverySourceCompactBinaryColumns : Fin 1 → Fin 24 → ℕ :=
  ![![7540978, 3434322, 3712930, 3983600, 7543026, 3096334, 7487314, 3590384, 1884191, 2592794,
    3093501, 3406607, 9036529, 1098004, 1136925, 303419, 9037325, 4135154, 252, 261995, 4024226,
    4106066, 254205, 1110031]]

/-- Complete original source data, retaining every coordinate. -/
def generatedTenthAxisLowerRecoverySourceCompactFullQPhase : Fin 1 → Fin 24 → ZMod 2 :=
  ![![0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1]]

/-- The source operator has all twelve genuine Fourier coordinates. -/
def generatedTenthAxisLowerRecoverySourceCompactHadamardRank : Fin 1 → Fin 13 := ![12]

/-- Exact full original source Pauli, including its central phase. -/
def generatedTenthAxisLowerRecoverySourceCompactPauliLabels :
    Fin 1 → Fin 4096 × Fin 4096 × ZMod 2 := ![(196, 1157, 0)]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

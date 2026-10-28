/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQFastMasks

/-! Ungated packed cocycle candidate metadata for joint9*1 and original10.
Rows were parsed from held genuine source columns and phases; binding needs Lean verification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The genuine joint nine times one and original ten compatible source fibers. -/
def generatedTenthTwoFixerCFiber : Fin 2 → localFiberSubgroup :=
  ![generatedTenthTwoFixerJointFiber, generatedTenthTwoFixerOriginalTenFiber]

/-- The complete binary columns for both original source automorphisms. -/
def generatedTenthTwoFixerCColumns : Fin 2 → Fin 24 → ℕ :=
  ![generatedTenthAxisLowerRecoveryJointCompactBinaryColumns 0,
    generatedTenthAxisLowerRecoveryCompactBinaryColumns 10]

/-- The genuine full unit images retain both base coordinates and central bits. -/
def generatedTenthTwoFixerCUnitImages : Fin 2 → Fin 24 → Q :=
  ![generatedTenthAxisLowerRecoveryJointCompactFullQCache 0,
    generatedTenthAxisLowerRecoveryCompactFullQCache 10]

/-- Candidate triangular cocycle rows, with all 24 original positions retained. -/
def generatedTenthTwoFixerCRows : Fin 2 → Fin 24 → ℕ :=
  ![
    ![3771422, 14001640, 12625336, 7348016, 8835488, 15088576, 421632, 817664, 4160000,
      12599296, 5847040, 5603328, 4227072, 4210688, 9830400, 13369344, 13238272, 14155776,
      6291456, 7340032, 0, 8388608, 8388608, 0],
    ![6068182, 11054984, 15542736, 4925472, 12391264, 16278848, 9256832, 11676416, 16173056,
      1497088, 9811968, 10969088, 1605632, 2867200, 819200, 12320768, 3145728, 9699328,
      13631488, 8388608, 10485760, 12582912, 0, 0]
  ]

/-- Candidate complete unit central bits, including the original source Pauli correction. -/
def generatedTenthTwoFixerCCoefficients : Fin 2 → ℕ :=
  ![10354831, 3184604]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

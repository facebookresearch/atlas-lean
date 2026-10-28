/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactData

/-! Complete original joint9*1 compact candidate data; numerical fixation is not a Lean proof. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The twelve retained left binary columns of the joint candidate. -/
def generatedTenthAxisLowerRecoveryJointCompactLeftColumns : Fin 1 → Fin 12 → ℕ :=
  ![![12, 2383, 3984, 4006, 972, 61, 963, 3036, 34, 3536, 1, 64]]

/-- The twelve retained inverse-left binary columns of the joint candidate. -/
def generatedTenthAxisLowerRecoveryJointCompactLeftInverseColumns : Fin 1 → Fin 12 → ℕ :=
  ![![1024, 1105, 124, 125, 368, 1361, 2048, 2983, 2482, 2564, 2181, 480]]

/-- The twelve retained right binary columns of the joint candidate. -/
def generatedTenthAxisLowerRecoveryJointCompactRightColumns : Fin 1 → Fin 12 → ℕ :=
  ![![1024, 2, 1029, 1033, 2048, 2096, 3153, 3089, 1153, 1281, 1025, 512]]

/-- The twelve retained inverse-right binary columns of the joint candidate. -/
def generatedTenthAxisLowerRecoveryJointCompactRightInverseColumns : Fin 1 → Fin 12 → ℕ :=
  ![![1025, 2, 1028, 1032, 1168, 1184, 192, 1280, 1536, 2048, 1, 16]]

/-- All rows of the retained first quadratic phase of the joint candidate. -/
def generatedTenthAxisLowerRecoveryJointCompactFirstPhaseRows : Fin 1 → Fin 12 → ℕ :=
  ![![1032, 2052, 1760, 3648, 1568, 2688, 256, 3072, 3584, 3072, 0, 0]]

/-- All rows of the retained second quadratic phase of the joint candidate. -/
def generatedTenthAxisLowerRecoveryJointCompactSecondPhaseRows : Fin 1 → Fin 12 → ℕ :=
  ![![2998, 432, 2344, 3440, 3936, 640, 2048, 1792, 3584, 0, 2048, 0]]

/-- All twenty-four retained full binary images of the joint candidate. -/
def generatedTenthAxisLowerRecoveryJointCompactBinaryColumns : Fin 1 → Fin 24 → ℕ :=
  ![![5253013, 313347, 3197728, 7838485, 1081431, 16364555, 7004225, 12160043, 7507993, 3983392,
    10187925, 3459075, 49164, 1362255, 15736720, 10452902, 13628364, 16195645, 15926211, 12046386,
    9386972, 14012450, 7579701, 466384]]

/-- All twenty-four retained central phase images of the joint candidate. -/
def generatedTenthAxisLowerRecoveryJointCompactFullQPhase : Fin 1 → Fin 24 → ZMod 2 :=
  ![![1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1]]

/-- The retained ten-coordinate Fourier rank of the joint candidate. -/
def generatedTenthAxisLowerRecoveryJointCompactHadamardRank : Fin 1 → Fin 13 := ![10]

/-- The retained translation, modulation, and central Pauli labels of the joint candidate. -/
def generatedTenthAxisLowerRecoveryJointCompactPauliLabels : Fin 1 → Fin 4096 × Fin 4096 × ZMod 2 :=
  ![(3541, 1430, 0)]

/-- The retained physical denominator four of the joint candidate. -/
def generatedTenthAxisLowerRecoveryJointCompactSpatialDenominator : Fin 1 → ℕ := ![4]

/-- All 576 retained integer physical entries of the joint candidate. -/
def generatedTenthAxisLowerRecoveryJointCompactSpatialNumerator : Fin 1 → Matrix (Fin 24) (Fin 24) ℤ
  :=
  ![![
    ![-1, 0, 0, -1, -1, 0, 2, 1, -1, 0, 2, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-1, 0, 2, 1, -1, 0, 0, -1, -1, 0, 0, -1, 1, 0, -2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, -2, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-1, 0, 0, -1, 1, 2, 0, -1, 1, 2, 0, -1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 2, -1, 1, 0, 0, 1, 1, 0, 0, 1, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 1, 1, 0, 2, -1, 1, 0, 2, -1, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 1, -1, 2, 0, 1, -1, 2, 0, 1, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-1, -2, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 2, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, -1, 0, 0, 1, -1, 0, 0, -1, 1, 0, 0, 1, -1, 0, -1, 1, 1, 1, -1, 1, -1, -1],
    ![0, 1, 1, 0, 0, 1, 1, 0, 0, -1, -1, 0, 0, 1, 1, 0, 1, 1, 1, 1, -1, -1, 1, 1],
    ![0, -1, -1, 0, 0, 1, 1, 0, 0, -1, -1, 0, 0, -1, -1, 0, -1, 1, -1, 1, 1, 1, 1, 1],
    ![0, -1, 1, 0, 0, 1, -1, 0, 0, -1, 1, 0, 0, -1, 1, 0, -1, -1, 1, -1, -1, 1, 1, 1],
    ![0, 1, 1, 0, 0, 1, 1, 0, 0, -1, -1, 0, 0, 1, 1, 0, -1, -1, -1, -1, 1, 1, -1, -1],
    ![0, 1, -1, 0, 0, 1, -1, 0, 0, -1, 1, 0, 0, 1, -1, 0, 1, -1, -1, -1, 1, -1, 1, 1],
    ![0, -1, 1, 0, 0, 1, -1, 0, 0, -1, 1, 0, 0, -1, 1, 0, 1, 1, -1, 1, 1, -1, -1, -1],
    ![0, -1, -1, 0, 0, 1, 1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 1, -1, 1, -1, -1, -1, -1, -1],
    ![-1, 0, 0, 1, -1, 0, 0, 1, 1, 0, 0, -1, -1, 0, 0, 1, -2, 0, 0, 0, 0, -2, 0, 0],
    ![-1, 0, 0, -1, -1, 0, 0, -1, 1, 0, 0, 1, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 2, -2],
    ![1, 0, 0, 1, -1, 0, 0, -1, 1, 0, 0, 1, 1, 0, 0, 1, 0, -2, 0, 2, 0, 0, 0, 0],
    ![1, 0, 0, -1, -1, 0, 0, 1, 1, 0, 0, -1, 1, 0, 0, -1, 0, 0, -2, 0, -2, 0, 0, 0],
    ![1, 0, 0, 1, 1, 0, 0, 1, -1, 0, 0, -1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, -2],
    ![1, 0, 0, -1, 1, 0, 0, -1, -1, 0, 0, 1, 1, 0, 0, -1, -2, 0, 0, 0, 0, -2, 0, 0],
    ![-1, 0, 0, 1, 1, 0, 0, -1, -1, 0, 0, 1, -1, 0, 0, 1, 0, 0, -2, 0, -2, 0, 0, 0],
    ![-1, 0, 0, -1, 1, 0, 0, 1, -1, 0, 0, -1, -1, 0, 0, -1, 0, -2, 0, 2, 0, 0, 0, 0]]]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

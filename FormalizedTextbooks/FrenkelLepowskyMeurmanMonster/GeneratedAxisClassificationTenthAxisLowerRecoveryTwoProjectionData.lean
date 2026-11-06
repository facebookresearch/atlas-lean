/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryJointCompactFoundation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryThreeProjectionGeneric

/-! Literal whole binary source words in joint9*1 and original10, with genuine inverses.
The discovery group order supplies no theorem premise. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- The literal original source candidates recognized by the two projected generators. -/
def generatedTenthAxisLowerRecoveryTwoProjectionCandidateIndex : Fin 3 → Fin 11 := ![1, 9, 10]

/-- All complete forward and inverse binary columns for the two projected generators. -/
def generatedTenthAxisLowerRecoveryTwoProjectionColumns : Fin 4 → Fin 24 → ℕ :=
  ![
    ![5253013, 313347, 3197728, 7838485, 1081431, 16364555, 7004225, 12160043, 7507993, 3983392,
      10187925, 3459075, 49164, 1362255, 15736720, 10452902, 13628364, 16195645, 15926211, 12046386,
      9386972, 14012450, 7579701, 466384],
    ![1459712, 11796389, 4935173, 9811473, 13198897, 6323687, 2598465, 6050631, 3352321, 3917888,
      3235905, 7825462, 960014, 8848470, 15731808, 4637815, 15141473, 9661015, 4661640, 5767798,
      3631680, 1030577, 6025231, 16124276],
    ![5409692, 4592952, 14967451, 12576403, 4886520, 5541368, 10529722, 7209240, 16504558, 12502244,
      1480308, 4850684, 14660706, 9118410, 4298043, 1704243, 5348772, 2639528, 330066, 4200796,
      55646, 53596, 4855820, 11070734],
    ![697856, 14133089, 15430952, 2401801, 16115570, 11829115, 9214811, 2705025, 16301476, 16132372,
      9129180, 108598, 6284856, 9045163, 9071787, 1089, 8489642, 8596124, 7211454, 139840, 1714752,
      1962417, 1568783, 10644276]]

/-- Complete original source words in the two generators and their genuine inverses. -/
def generatedTenthAxisLowerRecoveryTwoProjectionWords : Fin 3 → List (Fin 4) :=
  ![
    [3, 3, 0, 3, 3, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 0, 3, 3, 0, 0, 3, 3, 0, 1,
      1, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 0, 3, 3, 0, 0, 3, 3,
      0, 3, 3, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 0, 3, 3, 0, 0, 3, 3, 0, 1, 1, 0,
      3, 3, 0, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 0,
      3, 3, 0, 0, 3, 3, 0, 3, 3, 3, 3, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 0, 3, 3,
      0, 0, 3, 3, 0, 1, 1, 0, 3, 3, 0, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3,
      3, 0, 3, 3, 0, 0, 3, 3, 0, 1, 1, 0, 3, 3, 0, 1, 1, 2, 1, 1, 2, 3, 3, 2,
      1, 1, 2, 2, 1, 1, 2, 1, 1, 0, 3, 3, 0, 0, 3, 3, 0, 3, 3, 2, 1, 1, 2, 2,
      1, 1, 2, 3, 3, 0, 3, 3, 0, 0, 3, 3, 0, 1, 1, 0, 3, 3, 0, 1, 1, 1, 1, 2,
      1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 0, 3, 3, 0, 0, 3, 3, 0, 3,
      3, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 0, 3, 3, 0, 0, 3, 3, 0, 1, 1, 0, 3, 3,
      0, 3, 3, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 0, 3, 3, 0, 3,
      3, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 0, 3, 3, 0, 0, 3, 3, 0, 3, 3, 2, 1, 1,
      2, 2, 1, 1, 2, 3, 3, 0, 3, 3, 0, 0, 3, 3, 0, 1, 1, 0, 3, 3, 0, 3, 3, 0,
      3, 3, 0, 0, 3, 3, 0, 3, 3, 3, 3, 0, 3, 3, 0, 3, 0, 0, 1],
    [0, 3, 3, 0, 3, 3, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 0, 3, 3, 0, 0, 3, 3, 0,
      1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 0, 3, 3, 0, 0, 3,
      3, 0, 3, 3, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 0, 3, 3, 0, 0, 3, 3, 0, 1, 1,
      0, 3, 3, 0, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1,
      0, 3, 3, 0, 0, 3, 3, 0, 3, 3, 3, 3, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 0, 3,
      3, 0, 0, 3, 3, 0, 1, 1, 0, 3, 3, 0, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2,
      3, 3, 0, 3, 3, 0, 0, 3, 3, 0, 1, 1, 0, 3, 3, 0, 1, 1, 2, 1, 1, 2, 3, 3,
      2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 0, 3, 3, 0, 0, 3, 3, 0, 3, 3, 2, 1, 1, 2,
      2, 1, 1, 2, 3, 3, 0, 3, 3, 0, 0, 3, 3, 0, 1, 1, 0, 3, 3, 0, 1, 1, 1, 1,
      2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 0, 3, 3, 0, 0, 3, 3, 0,
      3, 3, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 0, 3, 3, 0, 0, 3, 3, 0, 1, 1, 0, 3,
      3, 0, 3, 3, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 0, 3, 3, 0,
      3, 3, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 0, 3, 3, 0, 0, 3, 3, 0, 3, 3, 2, 1,
      1, 2, 2, 1, 1, 2, 3, 3, 0, 3, 3, 0, 0, 3, 3, 0, 1, 1, 0, 3, 3, 0, 3, 3,
      0, 3, 3, 0, 0, 3, 3, 0, 3, 3, 3, 3, 0, 3, 3, 0, 3, 0, 0, 1],
    [1]
]

/-- Replay the entire two-generator word on the original full binary mask. -/
def generatedTenthAxisLowerRecoveryTwoProjectionMaskWord (w : List (Fin 4)) (v : ℕ) : ℕ :=
  w.foldr (fun g m => generatedAxisGlobalQMaskVector
    (generatedTenthAxisLowerRecoveryTwoProjectionColumns g) m) v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

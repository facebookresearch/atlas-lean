/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Checked actual Conway point images used in the chronological source-equation replay. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskOperators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskVectors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint071
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint080
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint089
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint092
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint093
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint096
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint097
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint098
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint099
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint103
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint112
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint113
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint116
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint122
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint123
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint124
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint126
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint130
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint131
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint133
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint134
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint135
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint138
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint140
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint257
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint258
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint261
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint263
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint264
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint266
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint268
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint271
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint274
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint275
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint280
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint281
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint282
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint288
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint289
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint290
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint291
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint296
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint300
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint304
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint306
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint310
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint315
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint317

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Binding 504 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction504 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint71 =
      monsterCo1GeometryVectorPoint257 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint71.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint71_binary,
    monsterCo1GeometryVectorPoint257_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 6864896 8179712
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 505 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction505 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint80 =
      monsterCo1GeometryVectorPoint258 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint80.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint80_binary,
    monsterCo1GeometryVectorPoint258_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 2816 4222984
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 506 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction506 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint89 =
      monsterCo1GeometryVectorPoint261 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint89.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint89_binary,
    monsterCo1GeometryVectorPoint261_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 5227504 424854
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 507 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction507 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint92 =
      monsterCo1GeometryVectorPoint263 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint92.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint92_binary,
    monsterCo1GeometryVectorPoint263_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 6815756 7590656
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 508 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction508 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint93 =
      monsterCo1GeometryVectorPoint264 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint93.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint93_binary,
    monsterCo1GeometryVectorPoint264_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 6866944 8181760
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 509 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction509 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint96 =
      monsterCo1GeometryVectorPoint266 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint96.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint96_binary,
    monsterCo1GeometryVectorPoint266_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 7365526 1849461
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 510 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction510 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint97 =
      monsterCo1GeometryVectorPoint268 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint97.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint97_binary,
    monsterCo1GeometryVectorPoint268_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 4194310 1100290
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 511 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction511 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint98 =
      monsterCo1GeometryVectorPoint271 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint98.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint98_binary,
    monsterCo1GeometryVectorPoint271_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 4587526 6015490
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 512 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction512 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint99 =
      monsterCo1GeometryVectorPoint274 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint99.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint99_binary,
    monsterCo1GeometryVectorPoint274_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 395270 1364482
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 513 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction513 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint103 =
      monsterCo1GeometryVectorPoint275 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint103.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint103_binary,
    monsterCo1GeometryVectorPoint275_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 4131824 4592534
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 514 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction514 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint112 =
      monsterCo1GeometryVectorPoint280 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint112.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint112_binary,
    monsterCo1GeometryVectorPoint280_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 396032 749576
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 515 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction515 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint113 =
      monsterCo1GeometryVectorPoint281 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint113.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint113_binary,
    monsterCo1GeometryVectorPoint281_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 4791040 5074952
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 516 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction516 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint116 =
      monsterCo1GeometryVectorPoint282 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint116.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint116_binary,
    monsterCo1GeometryVectorPoint282_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 4939776 5509120
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 517 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction517 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint122 =
      monsterCo1GeometryVectorPoint288 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint122.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint122_binary,
    monsterCo1GeometryVectorPoint288_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 7076863 4357221
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 518 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction518 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint123 =
      monsterCo1GeometryVectorPoint289 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint123.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint123_binary,
    monsterCo1GeometryVectorPoint289_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 2831347 157541
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 519 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction519 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint124 =
      monsterCo1GeometryVectorPoint290 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint124.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint124_binary,
    monsterCo1GeometryVectorPoint290_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 2605056 3522560
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 520 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction520 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint126 =
      monsterCo1GeometryVectorPoint291 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint126.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint126_binary,
    monsterCo1GeometryVectorPoint291_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 6799372 4903680
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 521 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction521 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint130 =
      monsterCo1GeometryVectorPoint296 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint130.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint130_binary,
    monsterCo1GeometryVectorPoint296_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 709122 5225226
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 522 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction522 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint131 =
      monsterCo1GeometryVectorPoint300 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint131.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint131_binary,
    monsterCo1GeometryVectorPoint300_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 4571650 637706
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 523 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction523 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint133 =
      monsterCo1GeometryVectorPoint304 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint133.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint133_binary,
    monsterCo1GeometryVectorPoint304_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 5056629 62496
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 524 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction524 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint134 =
      monsterCo1GeometryVectorPoint306 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint134.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint134_binary,
    monsterCo1GeometryVectorPoint306_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 1036802 4635402
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 525 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction525 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint135 =
      monsterCo1GeometryVectorPoint310 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint135.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint135_binary,
    monsterCo1GeometryVectorPoint310_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 4243970 47882
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 526 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction526 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint138 =
      monsterCo1GeometryVectorPoint315 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint138.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint138_binary,
    monsterCo1GeometryVectorPoint315_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 329740 3738368
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 527 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction527 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint140 =
      monsterCo1GeometryVectorPoint317 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint140.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint140_binary,
    monsterCo1GeometryVectorPoint317_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 4244464 31638
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

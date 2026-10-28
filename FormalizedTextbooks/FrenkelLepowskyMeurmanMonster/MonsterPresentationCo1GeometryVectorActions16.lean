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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint204
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint206
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint207
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint211
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint213
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint214
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint215
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint226
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint240
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint246
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint250
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint256
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint258
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint267
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint286
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint308
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint316
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint327
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint346
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint358
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint359
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint372
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint377
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint378
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint379
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint385
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint387
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint415
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint426
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint431
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint453
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint454
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint459
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint467
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint476
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint487
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint503
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint536
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint544
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint555
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint566
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint579
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint585
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint590
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint595
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint601
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint602
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint620

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Binding 384 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction384 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint204 =
      monsterCo1GeometryVectorPoint431 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint204.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint204_binary,
    monsterCo1GeometryVectorPoint431_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 748645 246885
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 385 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction385 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint206 =
      monsterCo1GeometryVectorPoint620 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint206.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint206_binary,
    monsterCo1GeometryVectorPoint620_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 6094731 8230795
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 386 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction386 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint207 =
      monsterCo1GeometryVectorPoint453 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint207.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint207_binary,
    monsterCo1GeometryVectorPoint453_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 568074 3672842
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 387 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction387 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint211 =
      monsterCo1GeometryVectorPoint226 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint211.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint211_binary,
    monsterCo1GeometryVectorPoint226_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 4628480 4630528
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 388 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction388 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint213 =
      monsterCo1GeometryVectorPoint415 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint213.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint213_binary,
    monsterCo1GeometryVectorPoint415_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 4841464 5040120
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 389 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction389 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint214 =
      monsterCo1GeometryVectorPoint536 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint214.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint214_binary,
    monsterCo1GeometryVectorPoint536_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 3362520 3808984
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 390 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction390 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint215 =
      monsterCo1GeometryVectorPoint459 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint215.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint215_binary,
    monsterCo1GeometryVectorPoint459_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 1188657 1798961
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 391 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction391 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint240 =
      monsterCo1GeometryVectorPoint426 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint240.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint240_binary,
    monsterCo1GeometryVectorPoint426_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 6556659 5782515
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 392 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction392 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint246 =
      monsterCo1GeometryVectorPoint454 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint246.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint246_binary,
    monsterCo1GeometryVectorPoint454_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 5155594 8258314
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 393 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction393 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint250 =
      monsterCo1GeometryVectorPoint467 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint250.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint250_binary,
    monsterCo1GeometryVectorPoint467_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 400142 1030926
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 394 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction394 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint256 =
      monsterCo1GeometryVectorPoint358 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint256.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint256_binary,
    monsterCo1GeometryVectorPoint358_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 8327936 7846656
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 395 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction395 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint258 =
      monsterCo1GeometryVectorPoint476 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint258.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint258_binary,
    monsterCo1GeometryVectorPoint476_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 4222984 7174152
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 396 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction396 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint267 =
      monsterCo1GeometryVectorPoint487 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint267.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint267_binary,
    monsterCo1GeometryVectorPoint487_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 4245398 7624598
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 397 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction397 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint286 =
      monsterCo1GeometryVectorPoint503 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint286.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint286_binary,
    monsterCo1GeometryVectorPoint503_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 6619128 6408184
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 398 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction398 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint308 =
      monsterCo1GeometryVectorPoint544 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint308.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint308_binary,
    monsterCo1GeometryVectorPoint544_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 4200972 5298700
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 399 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction399 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint316 =
      monsterCo1GeometryVectorPoint555 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint316.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint316_binary,
    monsterCo1GeometryVectorPoint555_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 6218545 5747505
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 400 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction400 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint327 =
      monsterCo1GeometryVectorPoint566 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint327.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint327_binary,
    monsterCo1GeometryVectorPoint566_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 5095774 7403870
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 401 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction401 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint346 =
      monsterCo1GeometryVectorPoint579 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint346.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint346_binary,
    monsterCo1GeometryVectorPoint579_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 6193159 7569415
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 402 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction402 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint359 =
      monsterCo1GeometryVectorPoint585 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint359.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint359_binary,
    monsterCo1GeometryVectorPoint585_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 7340800 7906048
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 403 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction403 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint372 =
      monsterCo1GeometryVectorPoint590 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint372.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint372_binary,
    monsterCo1GeometryVectorPoint590_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 5314574 5246990
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 404 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction404 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint377 =
      monsterCo1GeometryVectorPoint595 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint377.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint377_binary,
    monsterCo1GeometryVectorPoint595_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 4630538 8298506
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 405 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction405 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint378 =
      monsterCo1GeometryVectorPoint379 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint378.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint378_binary,
    monsterCo1GeometryVectorPoint379_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 7213056 7215104
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 406 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction406 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint385 =
      monsterCo1GeometryVectorPoint601 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint385.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint385_binary,
    monsterCo1GeometryVectorPoint601_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 4195086 4827918
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 407 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction407 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint387 =
      monsterCo1GeometryVectorPoint602 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint387.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint387_binary,
    monsterCo1GeometryVectorPoint602_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 3148558 3777294
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

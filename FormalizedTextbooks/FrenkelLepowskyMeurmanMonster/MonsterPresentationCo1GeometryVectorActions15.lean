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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint014
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint016
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint023
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint052
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint053
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint065
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint066
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint090
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint098
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint102
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint115
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint128
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint130
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint131
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint133
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint134
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint137
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint172
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint173
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint175
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint177
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint181
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint186
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint190
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint192
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint199
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint201
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint203
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint241
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint245
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint251
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint253
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint259
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint270
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint292
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint295
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint299
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint303
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint305
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint313
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint363
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint386
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint393
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint409
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint427
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint438
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint772

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Binding 360 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction360 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint52 =
      monsterCo1GeometryVectorPoint241 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint52.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint52_binary,
    monsterCo1GeometryVectorPoint241_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 6566899 5768179
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 361 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction361 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint53 =
      monsterCo1GeometryVectorPoint245 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint53.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint53_binary,
    monsterCo1GeometryVectorPoint245_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 4313602 5249538
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 362 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction362 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint65 =
      monsterCo1GeometryVectorPoint251 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint65.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint65_binary,
    monsterCo1GeometryVectorPoint251_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 4594432 5157632
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 363 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction363 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint66 =
      monsterCo1GeometryVectorPoint253 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint66.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint66_binary,
    monsterCo1GeometryVectorPoint253_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 3539862 170902
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 364 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction364 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint90 =
      monsterCo1GeometryVectorPoint115 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint90.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint90_binary,
    monsterCo1GeometryVectorPoint115_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 7073792 7075840
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 365 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction365 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint98 =
      monsterCo1GeometryVectorPoint270 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint98.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint98_binary,
    monsterCo1GeometryVectorPoint270_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 4587526 6948870
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 366 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction366 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint102 =
      monsterCo1GeometryVectorPoint259 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint102.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint102_binary,
    monsterCo1GeometryVectorPoint259_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 8375280 5764080
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 367 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction367 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint128 =
      monsterCo1GeometryVectorPoint292 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint128.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint128_binary,
    monsterCo1GeometryVectorPoint292_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 2555916 3344396
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 368 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction368 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint130 =
      monsterCo1GeometryVectorPoint295 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint130.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint130_binary,
    monsterCo1GeometryVectorPoint295_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 709122 1774082
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 369 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction369 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint131 =
      monsterCo1GeometryVectorPoint299 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint131.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint131_binary,
    monsterCo1GeometryVectorPoint299_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 4571650 5507586
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 370 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction370 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint133 =
      monsterCo1GeometryVectorPoint303 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint133.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint133_binary,
    monsterCo1GeometryVectorPoint303_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 5056629 4552821
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 371 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction371 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint134 =
      monsterCo1GeometryVectorPoint305 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint134.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint134_binary,
    monsterCo1GeometryVectorPoint305_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 1036802 1970690
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 372 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction372 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint137 =
      monsterCo1GeometryVectorPoint313 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint137.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint137_binary,
    monsterCo1GeometryVectorPoint313_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 770562 1704450
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 373 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction373 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint172 =
      monsterCo1GeometryVectorPoint363 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint172.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint172_binary,
    monsterCo1GeometryVectorPoint363_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 3197948 850940
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 374 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction374 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint173 =
      monsterCo1GeometryVectorPoint386 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint173.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint173_binary,
    monsterCo1GeometryVectorPoint386_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 6926 635662
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 375 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction375 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint175 =
      monsterCo1GeometryVectorPoint427 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint175.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint175_binary,
    monsterCo1GeometryVectorPoint427_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 6554623 4994047
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 376 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction376 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint177 =
      monsterCo1GeometryVectorPoint438 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint177.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint177_binary,
    monsterCo1GeometryVectorPoint438_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 922124 2021900
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 377 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction377 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint181 =
      monsterCo1GeometryVectorPoint409 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint181.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint181_binary,
    monsterCo1GeometryVectorPoint409_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 7497734 6184966
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 378 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction378 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint186 =
      monsterCo1GeometryVectorPoint772 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint186.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint186_binary,
    monsterCo1GeometryVectorPoint772_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 11725704 8879016
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 379 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction379 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint190 =
      monsterCo1GeometryVectorPoint14 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint190.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint190_binary,
    monsterCo1GeometryVectorPoint14_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 4766464 4201216
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 380 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction380 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint192 =
      monsterCo1GeometryVectorPoint16 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint192.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint192_binary,
    monsterCo1GeometryVectorPoint16_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 299926 3146646
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 381 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction381 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint199 =
      monsterCo1GeometryVectorPoint23 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint199.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint199_binary,
    monsterCo1GeometryVectorPoint23_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 8747960 11539352
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 382 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction382 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint201 =
      monsterCo1GeometryVectorPoint201 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint201.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint201_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 5312512 5312512
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 383 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction383 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint203 =
      monsterCo1GeometryVectorPoint393 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint203.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint203_binary,
    monsterCo1GeometryVectorPoint393_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 28680 2979848
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

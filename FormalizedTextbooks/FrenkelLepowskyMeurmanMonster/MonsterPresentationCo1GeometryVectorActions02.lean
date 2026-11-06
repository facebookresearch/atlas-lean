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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint168
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint169
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint172
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint173
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint177
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint181
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint183
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint184
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint186
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint187
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint190
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint192
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint193
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint195
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint197
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint199
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint200
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint201
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint203
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint204
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint205
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint206
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint207
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint208
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint219
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint270
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint273
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint346
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint349
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint354
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint361
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint372
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint380
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint385
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint391
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint396
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint429
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint435
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint441
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint446
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint451
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint463
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint523
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint527
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint532
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint618
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint771
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint776

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Binding 48 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction48 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint168 =
      monsterCo1GeometryVectorPoint346 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint168.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint168_binary,
    monsterCo1GeometryVectorPoint346_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 2000896 6193159
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 49 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction49 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint169 =
      monsterCo1GeometryVectorPoint349 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint169.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint169_binary,
    monsterCo1GeometryVectorPoint349_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 2654208 2654215
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 50 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction50 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint172 =
      monsterCo1GeometryVectorPoint361 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint172.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint172_binary,
    monsterCo1GeometryVectorPoint361_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 3197948 7341052
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 51 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction51 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint173 =
      monsterCo1GeometryVectorPoint385 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint173.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint173_binary,
    monsterCo1GeometryVectorPoint385_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 6926 4195086
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 52 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction52 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint177 =
      monsterCo1GeometryVectorPoint435 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint177.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint177_binary,
    monsterCo1GeometryVectorPoint435_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 922124 971278
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 53 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction53 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint181 =
      monsterCo1GeometryVectorPoint273 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint181.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint181_binary,
    monsterCo1GeometryVectorPoint273_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 7497734 3278854
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 54 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction54 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint183 =
      monsterCo1GeometryVectorPoint523 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint183.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint183_binary,
    monsterCo1GeometryVectorPoint523_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 3807349 8011902
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 55 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction55 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint184 =
      monsterCo1GeometryVectorPoint441 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint184.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint184_binary,
    monsterCo1GeometryVectorPoint441_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 2648578 6861318
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 56 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction56 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint186 =
      monsterCo1GeometryVectorPoint771 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint186.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint186_binary,
    monsterCo1GeometryVectorPoint771_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 11725704 15898497
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 57 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction57 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint187 =
      monsterCo1GeometryVectorPoint219 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint187.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint187_binary,
    monsterCo1GeometryVectorPoint219_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 5556236 1312780
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 58 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction58 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint190 =
      monsterCo1GeometryVectorPoint380 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint190.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint190_binary,
    monsterCo1GeometryVectorPoint380_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 4766464 572164
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 59 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction59 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint192 =
      monsterCo1GeometryVectorPoint396 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint192.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint192_binary,
    monsterCo1GeometryVectorPoint396_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 299926 324505
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 60 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction60 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint193 =
      monsterCo1GeometryVectorPoint270 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint193.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint193_binary,
    monsterCo1GeometryVectorPoint270_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 6971398 6948870
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 61 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction61 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint195 =
      monsterCo1GeometryVectorPoint527 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint195.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint195_binary,
    monsterCo1GeometryVectorPoint527_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 946293 925816
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 62 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction62 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint197 =
      monsterCo1GeometryVectorPoint446 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint197.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint197_binary,
    monsterCo1GeometryVectorPoint446_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 2032130 2085376
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 63 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction63 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint199 =
      monsterCo1GeometryVectorPoint776 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint199.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint199_binary,
    monsterCo1GeometryVectorPoint776_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 8747960 12912568
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 64 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction64 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint200 =
      monsterCo1GeometryVectorPoint354 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint200.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint200_binary,
    monsterCo1GeometryVectorPoint354_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 7344128 7346190
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 65 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction65 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint201 =
      monsterCo1GeometryVectorPoint372 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint201.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint201_binary,
    monsterCo1GeometryVectorPoint372_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 5312512 5314574
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 66 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction66 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint203 =
      monsterCo1GeometryVectorPoint391 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint203.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint203_binary,
    monsterCo1GeometryVectorPoint391_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 28680 8
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 67 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction67 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint204 =
      monsterCo1GeometryVectorPoint429 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint204.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint204_binary,
    monsterCo1GeometryVectorPoint429_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 748645 13316198
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 68 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction68 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint205 =
      monsterCo1GeometryVectorPoint532 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint205.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint205_binary,
    monsterCo1GeometryVectorPoint532_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 123936 8511521
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 69 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction69 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint206 =
      monsterCo1GeometryVectorPoint618 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint206.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint206_binary,
    monsterCo1GeometryVectorPoint618_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 6094731 10271631
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 70 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction70 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint207 =
      monsterCo1GeometryVectorPoint451 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint207.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint207_binary,
    monsterCo1GeometryVectorPoint451_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 568074 4719370
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 71 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction71 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint208 =
      monsterCo1GeometryVectorPoint463 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint208.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint208_binary,
    monsterCo1GeometryVectorPoint463_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 3525618 7672828
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

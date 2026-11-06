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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint184
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint186
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint189
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint190
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint192
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint193
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint195
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint197
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint199
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint200
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint201
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint204
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint205
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint206
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint207
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint208
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint209
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint211
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint213
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint214
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint215
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint217
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint218
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint219
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint351
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint355
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint357
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint358
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint373
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint378
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint381
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint397
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint412
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint416
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint432
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint442
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint448
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint455
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint460
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint464
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint528
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint533
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint537
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint621
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint774
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint778
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint781

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Binding 552 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction552 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint184 =
      monsterCo1GeometryVectorPoint442 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint184.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint184_binary,
    monsterCo1GeometryVectorPoint442_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 2648578 2712330
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 553 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction553 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint186 =
      monsterCo1GeometryVectorPoint774 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint186.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint186_binary,
    monsterCo1GeometryVectorPoint774_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 11725704 16372555
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 554 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction554 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint189 =
      monsterCo1GeometryVectorPoint351 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint189.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint189_binary,
    monsterCo1GeometryVectorPoint351_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 8177676 3435264
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 555 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction555 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint190 =
      monsterCo1GeometryVectorPoint381 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint190.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint190_binary,
    monsterCo1GeometryVectorPoint381_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 4766464 6713352
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 556 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction556 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint192 =
      monsterCo1GeometryVectorPoint397 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint192.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint192_binary,
    monsterCo1GeometryVectorPoint397_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 299926 5798005
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 557 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction557 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint193 =
      monsterCo1GeometryVectorPoint412 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint193.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint193_binary,
    monsterCo1GeometryVectorPoint412_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 6971398 4852226
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 558 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction558 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint195 =
      monsterCo1GeometryVectorPoint528 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint195.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint195_binary,
    monsterCo1GeometryVectorPoint528_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 946293 1362976
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 559 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction559 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint197 =
      monsterCo1GeometryVectorPoint448 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint197.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint197_binary,
    monsterCo1GeometryVectorPoint448_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 2032130 4594442
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 560 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction560 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint199 =
      monsterCo1GeometryVectorPoint778 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint199.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint199_binary,
    monsterCo1GeometryVectorPoint778_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 8747960 16542298
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 561 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction561 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint200 =
      monsterCo1GeometryVectorPoint355 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint200.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint200_binary,
    monsterCo1GeometryVectorPoint355_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 7344128 7368704
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 562 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction562 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint201 =
      monsterCo1GeometryVectorPoint373 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint201.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint201_binary,
    monsterCo1GeometryVectorPoint373_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 5312512 3256320
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 563 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction563 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint204 =
      monsterCo1GeometryVectorPoint432 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint204.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint204_binary,
    monsterCo1GeometryVectorPoint432_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 748645 2953454
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 564 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction564 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint205 =
      monsterCo1GeometryVectorPoint533 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint205.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint205_binary,
    monsterCo1GeometryVectorPoint533_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 123936 1777119
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 565 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction565 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint206 =
      monsterCo1GeometryVectorPoint621 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint206.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint206_binary,
    monsterCo1GeometryVectorPoint621_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 6094731 3270726
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 566 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction566 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint207 =
      monsterCo1GeometryVectorPoint455 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint207.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint207_binary,
    monsterCo1GeometryVectorPoint455_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 568074 4827402
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 567 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction567 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint208 =
      monsterCo1GeometryVectorPoint464 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint208.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint208_binary,
    monsterCo1GeometryVectorPoint464_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 3525618 4587672
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 568 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction568 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint209 =
      monsterCo1GeometryVectorPoint781 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint209.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint209_binary,
    monsterCo1GeometryVectorPoint781_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 11991163 12469294
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 569 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction569 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint211 =
      monsterCo1GeometryVectorPoint378 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint211.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint211_binary,
    monsterCo1GeometryVectorPoint378_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 4628480 7213056
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 570 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction570 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint213 =
      monsterCo1GeometryVectorPoint416 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint213.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint213_binary,
    monsterCo1GeometryVectorPoint416_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 4841464 1928804
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 571 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction571 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint214 =
      monsterCo1GeometryVectorPoint537 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint214.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint214_binary,
    monsterCo1GeometryVectorPoint537_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 3362520 7144521
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 572 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction572 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint215 =
      monsterCo1GeometryVectorPoint460 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint215.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint215_binary,
    monsterCo1GeometryVectorPoint460_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 1188657 6942436
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 573 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction573 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint217 =
      monsterCo1GeometryVectorPoint357 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint217.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint217_binary,
    monsterCo1GeometryVectorPoint357_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 3543040 7626752
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 574 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction574 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint218 =
      monsterCo1GeometryVectorPoint358 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint218.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint218_binary,
    monsterCo1GeometryVectorPoint358_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 1361932 7846656
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 575 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction575 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint219 =
      monsterCo1GeometryVectorPoint190 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint219.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint219_binary,
    monsterCo1GeometryVectorPoint190_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 1312780 4766464
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

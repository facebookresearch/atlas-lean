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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint303
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint304
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint306
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint307
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint308
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint309
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint310
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint311
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint313
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint315
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint317
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint325
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint332
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint335
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint336
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint338
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint340
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint341
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint342
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint353
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint360
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint368
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint369
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint371
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint373
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint483
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint495
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint534
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint541
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint542
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint545
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint546
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint548
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint550
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint552
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint554
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint556
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint564
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint567
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint568
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint570
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint571
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint573
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint574
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint575
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint586
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint589
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint591

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Binding 624 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction624 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint304 =
      monsterCo1GeometryVectorPoint534 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint304.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint304_binary,
    monsterCo1GeometryVectorPoint534_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 62496 5574111
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 625 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction625 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint306 =
      monsterCo1GeometryVectorPoint541 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint306.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint306_binary,
    monsterCo1GeometryVectorPoint541_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 4635402 5155082
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 626 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction626 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint307 =
      monsterCo1GeometryVectorPoint542 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint307.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint307_binary,
    monsterCo1GeometryVectorPoint542_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 3343153 7020260
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 627 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction627 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint308 =
      monsterCo1GeometryVectorPoint545 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint308.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint308_binary,
    monsterCo1GeometryVectorPoint545_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 4200972 3191556
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 628 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction628 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint309 =
      monsterCo1GeometryVectorPoint546 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint309.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint309_binary,
    monsterCo1GeometryVectorPoint546_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 6711810 2192138
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 629 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction629 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint310 =
      monsterCo1GeometryVectorPoint548 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint310.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint310_binary,
    monsterCo1GeometryVectorPoint548_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 47882 4897034
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 630 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction630 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint311 =
      monsterCo1GeometryVectorPoint550 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint311.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint311_binary,
    monsterCo1GeometryVectorPoint550_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 5030705 2981604
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 631 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction631 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint313 =
      monsterCo1GeometryVectorPoint552 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint313.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint313_binary,
    monsterCo1GeometryVectorPoint552_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 1704450 5184266
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 632 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction632 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint315 =
      monsterCo1GeometryVectorPoint554 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint315.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint315_binary,
    monsterCo1GeometryVectorPoint554_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 3738368 3997704
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 633 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction633 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint317 =
      monsterCo1GeometryVectorPoint556 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint317.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint317_binary,
    monsterCo1GeometryVectorPoint556_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 31638 7094389
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 634 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction634 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint325 =
      monsterCo1GeometryVectorPoint564 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint325.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint325_binary,
    monsterCo1GeometryVectorPoint564_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 5033984 3866624
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 635 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction635 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint332 =
      monsterCo1GeometryVectorPoint567 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint332.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint332_binary,
    monsterCo1GeometryVectorPoint567_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 5317629 8193899
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 636 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction636 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint335 =
      monsterCo1GeometryVectorPoint568 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint335.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint335_binary,
    monsterCo1GeometryVectorPoint568_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 3152790 602229
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 637 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction637 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint336 =
      monsterCo1GeometryVectorPoint570 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint336.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint336_binary,
    monsterCo1GeometryVectorPoint570_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 7724018 393368
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 638 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction638 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint338 =
      monsterCo1GeometryVectorPoint571 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint338.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint338_binary,
    monsterCo1GeometryVectorPoint571_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 7659520 4935680
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 639 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction639 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint340 =
      monsterCo1GeometryVectorPoint573 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint340.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint340_binary,
    monsterCo1GeometryVectorPoint573_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 332798 7760792
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 640 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction640 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint341 =
      monsterCo1GeometryVectorPoint574 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint341.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint341_binary,
    monsterCo1GeometryVectorPoint574_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 7764886 5775477
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 641 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction641 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint342 =
      monsterCo1GeometryVectorPoint575 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint342.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint342_binary,
    monsterCo1GeometryVectorPoint575_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 192512 7348224
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 642 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction642 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint353 =
      monsterCo1GeometryVectorPoint483 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint353.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint353_binary,
    monsterCo1GeometryVectorPoint483_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 5232652 4786944
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 643 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction643 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint360 =
      monsterCo1GeometryVectorPoint586 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint360.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint360_binary,
    monsterCo1GeometryVectorPoint586_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 58262 4876405
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 644 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction644 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint368 =
      monsterCo1GeometryVectorPoint495 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint368.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint368_binary,
    monsterCo1GeometryVectorPoint495_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 5230606 7933966
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 645 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction645 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint369 =
      monsterCo1GeometryVectorPoint303 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint369.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint369_binary,
    monsterCo1GeometryVectorPoint303_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 62358 4552821
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 646 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction646 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint371 =
      monsterCo1GeometryVectorPoint589 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint371.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint371_binary,
    monsterCo1GeometryVectorPoint589_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 4237206 1281931
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 647 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction647 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint373 =
      monsterCo1GeometryVectorPoint591 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint373.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint373_binary,
    monsterCo1GeometryVectorPoint591_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 3256320 1335296
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

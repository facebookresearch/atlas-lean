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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint388
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint389
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint390
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint406
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint408
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint414
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint420
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint429
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint433
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint434
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint439
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint455
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint460
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint468
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint475
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint486
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint488
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint497
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint505
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint506
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint508
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint509
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint515
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint526
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint533
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint563
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint589
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint599
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint603
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint616
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint628
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint637
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint645
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint649
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint650
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint659
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint664
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint678
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint685
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint691
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint700
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint702
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint708
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint712
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint713
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint714
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint715
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint733

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Binding 408 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction408 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint388 =
      monsterCo1GeometryVectorPoint603 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint388.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint388_binary,
    monsterCo1GeometryVectorPoint603_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 746246 3132166
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 409 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction409 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint389 =
      monsterCo1GeometryVectorPoint475 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint389.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint389_binary,
    monsterCo1GeometryVectorPoint475_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 5994504 7763976
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 410 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction410 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint390 =
      monsterCo1GeometryVectorPoint563 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint390.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint390_binary,
    monsterCo1GeometryVectorPoint563_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 1200382 3391742
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 411 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction411 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint406 =
      monsterCo1GeometryVectorPoint616 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint406.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint406_binary,
    monsterCo1GeometryVectorPoint616_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 16169874 16505778
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 412 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction412 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint408 =
      monsterCo1GeometryVectorPoint589 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint408.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint408_binary,
    monsterCo1GeometryVectorPoint589_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 3338123 1281931
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 413 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction413 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint414 =
      monsterCo1GeometryVectorPoint628 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint414.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint414_binary,
    monsterCo1GeometryVectorPoint628_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 9022450 11822034
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 414 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction414 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint420 =
      monsterCo1GeometryVectorPoint637 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint420.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint420_binary,
    monsterCo1GeometryVectorPoint637_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 6228482 5163522
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 415 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction415 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint429 =
      monsterCo1GeometryVectorPoint645 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint429.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint429_binary,
    monsterCo1GeometryVectorPoint645_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 13316198 14116934
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 416 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction416 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint433 =
      monsterCo1GeometryVectorPoint649 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint433.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint433_binary,
    monsterCo1GeometryVectorPoint649_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 2636488 2200264
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 417 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction417 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint434 =
      monsterCo1GeometryVectorPoint650 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint434.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint434_binary,
    monsterCo1GeometryVectorPoint650_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 5763638 8374838
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 418 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction418 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint439 =
      monsterCo1GeometryVectorPoint659 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint439.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint439_binary,
    monsterCo1GeometryVectorPoint659_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 3713796 590596
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 419 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction419 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint455 =
      monsterCo1GeometryVectorPoint678 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint455.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint455_binary,
    monsterCo1GeometryVectorPoint678_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 4827402 8243466
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 420 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction420 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint460 =
      monsterCo1GeometryVectorPoint685 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint460.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint460_binary,
    monsterCo1GeometryVectorPoint685_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 6942436 7620324
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 421 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction421 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint468 =
      monsterCo1GeometryVectorPoint599 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint468.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint468_binary,
    monsterCo1GeometryVectorPoint599_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 4917256 6686728
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 422 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction422 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint486 =
      monsterCo1GeometryVectorPoint700 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint486.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint486_binary,
    monsterCo1GeometryVectorPoint700_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 12626844 13421500
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 423 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction423 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint488 =
      monsterCo1GeometryVectorPoint702 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint488.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint488_binary,
    monsterCo1GeometryVectorPoint702_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 4624267 6811531
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 424 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction424 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint497 =
      monsterCo1GeometryVectorPoint708 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint497.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint497_binary,
    monsterCo1GeometryVectorPoint708_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 4636684 5425164
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 425 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction425 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint505 =
      monsterCo1GeometryVectorPoint712 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint505.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint505_binary,
    monsterCo1GeometryVectorPoint712_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 6417096 6832840
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 426 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction426 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint506 =
      monsterCo1GeometryVectorPoint713 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint506.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint506_binary,
    monsterCo1GeometryVectorPoint713_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 1974838 3545654
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 427 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction427 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint508 =
      monsterCo1GeometryVectorPoint714 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint508.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint508_binary,
    monsterCo1GeometryVectorPoint714_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 4905730 5733122
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 428 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction428 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint509 =
      monsterCo1GeometryVectorPoint715 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint509.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint509_binary,
    monsterCo1GeometryVectorPoint715_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 8366858 5178122
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 429 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction429 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint515 =
      monsterCo1GeometryVectorPoint664 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint515.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint515_binary,
    monsterCo1GeometryVectorPoint664_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 1666788 313060
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 430 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction430 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint526 =
      monsterCo1GeometryVectorPoint691 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint526.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint526_binary,
    monsterCo1GeometryVectorPoint691_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 1658584 1054424
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 431 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction431 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint533 =
      monsterCo1GeometryVectorPoint733 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint533.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint533_binary,
    monsterCo1GeometryVectorPoint733_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 1777119 3663327
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

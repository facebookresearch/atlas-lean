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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint301
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint305
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint308
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint311
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint314
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint319
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint320
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint323
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint339
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint345
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint347
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint348
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint363
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint369
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint371
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint375
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint378
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint381
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint382
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint384
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint385
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint394
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint395
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint402
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint427
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint473
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint521
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint538
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint543
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint549
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint553
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint554
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint558
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint559
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint562
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint572
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint578
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint581
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint582
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint587
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint588
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint592
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint597
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint599
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint605
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint606
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint611

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Binding 96 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction96 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint301 =
      monsterCo1GeometryVectorPoint521 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint301.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint301_binary,
    monsterCo1GeometryVectorPoint521_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 8373041 8334140
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 97 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction97 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint305 =
      monsterCo1GeometryVectorPoint538 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint305.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint305_binary,
    monsterCo1GeometryVectorPoint538_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 1970690 2015758
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 98 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction98 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint308 =
      monsterCo1GeometryVectorPoint543 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint308.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint308_binary,
    monsterCo1GeometryVectorPoint543_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 4200972 55822
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 99 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction99 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint311 =
      monsterCo1GeometryVectorPoint549 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint311.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint311_binary,
    monsterCo1GeometryVectorPoint549_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 5030705 4991804
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 100 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction100 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint314 =
      monsterCo1GeometryVectorPoint553 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint314.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint314_binary,
    monsterCo1GeometryVectorPoint553_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 2171697 2212669
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 101 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction101 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint319 =
      monsterCo1GeometryVectorPoint558 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint319.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint319_binary,
    monsterCo1GeometryVectorPoint558_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 4447218 199666
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 102 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction102 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint320 =
      monsterCo1GeometryVectorPoint559 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint320.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint320_binary,
    monsterCo1GeometryVectorPoint559_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 524638 528720
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 103 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction103 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint323 =
      monsterCo1GeometryVectorPoint562 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint323.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint323_binary,
    monsterCo1GeometryVectorPoint562_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 4358144 4360199
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 104 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction104 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint339 =
      monsterCo1GeometryVectorPoint572 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint339.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint339_binary,
    monsterCo1GeometryVectorPoint572_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 5368817 1117169
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 105 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction105 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint345 =
      monsterCo1GeometryVectorPoint578 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint345.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint345_binary,
    monsterCo1GeometryVectorPoint578_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 4108288 4108292
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 106 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction106 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint347 =
      monsterCo1GeometryVectorPoint581 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint347.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint347_binary,
    monsterCo1GeometryVectorPoint581_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 6195200 2000903
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 107 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction107 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint348 =
      monsterCo1GeometryVectorPoint582 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint348.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint348_binary,
    monsterCo1GeometryVectorPoint582_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 4110336 8302596
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 108 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction108 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint363 =
      monsterCo1GeometryVectorPoint427 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint363.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint363_binary,
    monsterCo1GeometryVectorPoint427_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 850940 4994047
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 109 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction109 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint369 =
      monsterCo1GeometryVectorPoint587 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint369.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint369_binary,
    monsterCo1GeometryVectorPoint587_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 62358 37791
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 110 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction110 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint371 =
      monsterCo1GeometryVectorPoint588 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint371.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint371_binary,
    monsterCo1GeometryVectorPoint588_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 4237206 12635034
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 111 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction111 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint375 =
      monsterCo1GeometryVectorPoint592 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint375.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint375_binary,
    monsterCo1GeometryVectorPoint592_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 6406144 6408204
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 112 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction112 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint378 =
      monsterCo1GeometryVectorPoint597 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint378.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint378_binary,
    monsterCo1GeometryVectorPoint597_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 7213056 7215118
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 113 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction113 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint381 =
      monsterCo1GeometryVectorPoint599 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint381.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint381_binary,
    monsterCo1GeometryVectorPoint599_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 6713352 6686728
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 114 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction114 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint382 =
      monsterCo1GeometryVectorPoint554 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint382.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint382_binary,
    monsterCo1GeometryVectorPoint554_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 4026376 3997704
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 115 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction115 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint384 =
      monsterCo1GeometryVectorPoint473 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint384.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint384_binary,
    monsterCo1GeometryVectorPoint473_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 720904 749568
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 116 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction116 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint385 =
      monsterCo1GeometryVectorPoint14 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint385.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint385_binary,
    monsterCo1GeometryVectorPoint14_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 4195086 4201216
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 117 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction117 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint394 =
      monsterCo1GeometryVectorPoint605 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint394.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint394_binary,
    monsterCo1GeometryVectorPoint605_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 1032 8417280
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 118 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction118 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint395 =
      monsterCo1GeometryVectorPoint606 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint395.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint395_binary,
    monsterCo1GeometryVectorPoint606_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 7787528 16164866
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 119 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction119 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint402 =
      monsterCo1GeometryVectorPoint611 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint402.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint402_binary,
    monsterCo1GeometryVectorPoint611_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 1011822 1007720
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

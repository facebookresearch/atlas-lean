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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint280
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint282
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint288
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint289
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint294
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint299
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint300
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint303
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint305
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint312
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint321
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint322
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint324
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint326
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint328
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint329
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint330
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint331
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint333
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint334
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint335
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint343
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint344
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint346
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint350
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint487
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint498
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint499
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint505
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint506
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint507
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint510
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint517
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint520
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint531
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint539
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint551
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint558
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint559
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint561
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint563
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint565
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint569
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint576
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint577
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint580
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint583

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Binding 840 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction840 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint280 =
      monsterCo1GeometryVectorPoint498 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint280.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint280_binary,
    monsterCo1GeometryVectorPoint498_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 749576 2958344
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 841 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction841 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint282 =
      monsterCo1GeometryVectorPoint499 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint282.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint282_binary,
    monsterCo1GeometryVectorPoint499_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 5509120 5423104
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 842 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction842 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint288 =
      monsterCo1GeometryVectorPoint505 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint288.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint288_binary,
    monsterCo1GeometryVectorPoint505_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 4357221 6417096
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 843 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction843 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint289 =
      monsterCo1GeometryVectorPoint506 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint289.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint289_binary,
    monsterCo1GeometryVectorPoint506_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 157541 1974838
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 844 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction844 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint294 =
      monsterCo1GeometryVectorPoint510 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint294.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint294_binary,
    monsterCo1GeometryVectorPoint510_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 2914818 432945
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 845 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction845 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint299 =
      monsterCo1GeometryVectorPoint517 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint299.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint299_binary,
    monsterCo1GeometryVectorPoint517_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 5507586 7211825
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 846 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction846 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint300 =
      monsterCo1GeometryVectorPoint520 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint300.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint300_binary,
    monsterCo1GeometryVectorPoint520_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 637706 3743498
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 847 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction847 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint303 =
      monsterCo1GeometryVectorPoint531 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint303.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint303_binary,
    monsterCo1GeometryVectorPoint531_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 4552821 6745816
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 848 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction848 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint305 =
      monsterCo1GeometryVectorPoint539 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint305.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint305_binary,
    monsterCo1GeometryVectorPoint539_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 1970690 2278193
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 849 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction849 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint312 =
      monsterCo1GeometryVectorPoint551 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint312.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint312_binary,
    monsterCo1GeometryVectorPoint551_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 2974210 2601777
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 850 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction850 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint321 =
      monsterCo1GeometryVectorPoint559 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint321.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint321_binary,
    monsterCo1GeometryVectorPoint559_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 2371587 528720
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 851 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction851 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint322 =
      monsterCo1GeometryVectorPoint561 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint322.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint322_binary,
    monsterCo1GeometryVectorPoint561_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 6027279 4704604
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 852 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction852 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint324 =
      monsterCo1GeometryVectorPoint563 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint324.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint324_binary,
    monsterCo1GeometryVectorPoint563_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 705280 3391742
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 853 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction853 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint326 =
      monsterCo1GeometryVectorPoint565 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint326.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint326_binary,
    monsterCo1GeometryVectorPoint565_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 4360192 7620608
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 854 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction854 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint329 =
      monsterCo1GeometryVectorPoint507 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint329.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint329_binary,
    monsterCo1GeometryVectorPoint507_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 3563520 421888
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 855 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction855 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint330 =
      monsterCo1GeometryVectorPoint330 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint330.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint330_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 3170304 3170304
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 856 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction856 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint331 =
      monsterCo1GeometryVectorPoint558 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint331.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint331_binary,
    monsterCo1GeometryVectorPoint558_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 383986 199666
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 857 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction857 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint333 =
      monsterCo1GeometryVectorPoint487 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint333.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint333_binary,
    monsterCo1GeometryVectorPoint487_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 4383638 7624598
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 858 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction858 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint334 =
      monsterCo1GeometryVectorPoint328 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint334.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint334_binary,
    monsterCo1GeometryVectorPoint328_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 8051698 5037042
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 859 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction859 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint335 =
      monsterCo1GeometryVectorPoint569 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint335.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint335_binary,
    monsterCo1GeometryVectorPoint569_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 3152790 32662
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 860 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction860 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint343 =
      monsterCo1GeometryVectorPoint576 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint343.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint343_binary,
    monsterCo1GeometryVectorPoint576_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 1998855 3409236
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 861 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction861 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint344 =
      monsterCo1GeometryVectorPoint577 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint344.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint344_binary,
    monsterCo1GeometryVectorPoint577_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 6193152 8286208
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 862 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction862 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint346 =
      monsterCo1GeometryVectorPoint580 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint346.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint346_binary,
    monsterCo1GeometryVectorPoint580_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 6193159 7652692
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 863 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction863 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint350 =
      monsterCo1GeometryVectorPoint583 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint350.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint350_binary,
    monsterCo1GeometryVectorPoint583_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 2488320 1308672
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

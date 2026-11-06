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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint411
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint415
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint416
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint429
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint438
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint440
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint442
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint443
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint446
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint449
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint450
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint453
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint458
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint460
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint471
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint474
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint482
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint485
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint490
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint491
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint499
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint513
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint518
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint532
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint537
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint585
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint601
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint603
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint625
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint631
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint632
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint643
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint658
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint661
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint662
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint666
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint672
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint673
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint682
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint684
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint692
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint698
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint704
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint705
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint708
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint714
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint729
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint736

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Binding 120 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction120 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint411 =
      monsterCo1GeometryVectorPoint625 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint411.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint411_binary,
    monsterCo1GeometryVectorPoint625_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 7073784 11246577
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 121 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction121 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint415 =
      monsterCo1GeometryVectorPoint631 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint415.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint415_binary,
    monsterCo1GeometryVectorPoint631_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 5040120 13409265
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 122 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction122 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint416 =
      monsterCo1GeometryVectorPoint632 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint416.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint416_binary,
    monsterCo1GeometryVectorPoint632_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 1928804 14537318
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 123 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction123 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint429 =
      monsterCo1GeometryVectorPoint643 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint429.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint429_binary,
    monsterCo1GeometryVectorPoint643_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 13316198 13327459
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 124 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction124 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint438 =
      monsterCo1GeometryVectorPoint658 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint438.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint438_binary,
    monsterCo1GeometryVectorPoint658_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 2021900 6164994
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 125 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction125 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint440 =
      monsterCo1GeometryVectorPoint661 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint440.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint440_binary,
    monsterCo1GeometryVectorPoint661_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 3006657 2949313
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 126 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction126 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint442 =
      monsterCo1GeometryVectorPoint662 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint442.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint442_binary,
    monsterCo1GeometryVectorPoint662_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 2712330 2736902
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 127 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction127 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint443 =
      monsterCo1GeometryVectorPoint603 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint443.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint443_binary,
    monsterCo1GeometryVectorPoint603_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 7301898 3132166
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 128 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction128 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint446 =
      monsterCo1GeometryVectorPoint666 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint446.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint446_binary,
    monsterCo1GeometryVectorPoint666_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 2085376 2085378
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 129 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction129 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint449 =
      monsterCo1GeometryVectorPoint672 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint449.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint449_binary,
    monsterCo1GeometryVectorPoint672_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 254769 197425
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 130 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction130 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint450 =
      monsterCo1GeometryVectorPoint673 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint450.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint450_binary,
    monsterCo1GeometryVectorPoint673_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 8137521 3984189
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 131 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction131 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint453 =
      monsterCo1GeometryVectorPoint585 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint453.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint453_binary,
    monsterCo1GeometryVectorPoint585_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 3672842 7906048
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 132 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction132 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint458 =
      monsterCo1GeometryVectorPoint682 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint458.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint458_binary,
    monsterCo1GeometryVectorPoint682_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 1229629 1237820
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 133 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction133 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint460 =
      monsterCo1GeometryVectorPoint684 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint460.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint460_binary,
    monsterCo1GeometryVectorPoint684_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 6942436 11098849
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 134 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction134 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint471 =
      monsterCo1GeometryVectorPoint692 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint471.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint471_binary,
    monsterCo1GeometryVectorPoint692_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 6884964 11123296
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 135 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction135 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint474 =
      monsterCo1GeometryVectorPoint482 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint474.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint474_binary,
    monsterCo1GeometryVectorPoint482_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 7995392 7997440
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 136 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction136 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint485 =
      monsterCo1GeometryVectorPoint698 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint485.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint485_binary,
    monsterCo1GeometryVectorPoint698_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 3228704 11616299
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 137 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction137 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint490 =
      monsterCo1GeometryVectorPoint704 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint490.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint490_binary,
    monsterCo1GeometryVectorPoint704_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 222820 8639078
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 138 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction138 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint491 =
      monsterCo1GeometryVectorPoint705 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint491.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint491_binary,
    monsterCo1GeometryVectorPoint705_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 7800420 16235104
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 139 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction139 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint499 =
      monsterCo1GeometryVectorPoint708 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint499.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint499_binary,
    monsterCo1GeometryVectorPoint708_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 5423104 5425164
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 140 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction140 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint513 =
      monsterCo1GeometryVectorPoint714 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint513.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint513_binary,
    monsterCo1GeometryVectorPoint714_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 5755658 5733122
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 141 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction141 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint518 =
      monsterCo1GeometryVectorPoint601 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint518.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint518_binary,
    monsterCo1GeometryVectorPoint601_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 4788996 4827918
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 142 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction142 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint532 =
      monsterCo1GeometryVectorPoint729 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint532.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint532_binary,
    monsterCo1GeometryVectorPoint729_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 8511521 8455201
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 143 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction143 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint537 =
      monsterCo1GeometryVectorPoint736 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint537.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint537_binary,
    monsterCo1GeometryVectorPoint736_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 7144521 15571008
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

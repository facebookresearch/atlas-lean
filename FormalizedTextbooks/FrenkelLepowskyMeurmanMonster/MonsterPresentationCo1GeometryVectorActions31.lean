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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint000
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint001
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint002
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint003
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint004
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint005
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint006
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint007
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint008
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint009
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint010
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint011
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint012
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint013
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint014
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint015
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint016
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint017
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint018
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint019
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint020
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint021
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint022
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint104
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint165
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint210
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint211
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint212
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint213
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint214
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint215
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint641
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint841

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Binding 744 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction744 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint841 =
      monsterCo1GeometryVectorPoint641 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint841.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint841_binary,
    monsterCo1GeometryVectorPoint641_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 1519329 7739561
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 745 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction745 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint0 =
      monsterCo1GeometryVectorPoint0 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint0.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint0_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 2048 2048
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 746 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction746 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint1 =
      monsterCo1GeometryVectorPoint3 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint1.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint1_binary,
    monsterCo1GeometryVectorPoint3_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 4194304 4243456
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 747 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction747 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint2 =
      monsterCo1GeometryVectorPoint6 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint2.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint2_binary,
    monsterCo1GeometryVectorPoint6_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 5181440 8372224
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 748 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction748 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint3 =
      monsterCo1GeometryVectorPoint1 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint3.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint3_binary,
    monsterCo1GeometryVectorPoint1_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 4243456 4194304
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 749 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction749 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint4 =
      monsterCo1GeometryVectorPoint11 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint4.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint4_binary,
    monsterCo1GeometryVectorPoint11_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 5183502 7392240
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 750 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction750 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint5 =
      monsterCo1GeometryVectorPoint210 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint5.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint5_binary,
    monsterCo1GeometryVectorPoint210_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 4587520 7786496
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 751 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction751 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint6 =
      monsterCo1GeometryVectorPoint2 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint6.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint6_binary,
    monsterCo1GeometryVectorPoint2_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 8372224 5181440
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 752 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction752 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint7 =
      monsterCo1GeometryVectorPoint7 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint7.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint7_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 4245516 4245516
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 753 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction753 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint8 =
      monsterCo1GeometryVectorPoint104 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint8.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint8_binary,
    monsterCo1GeometryVectorPoint104_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 985102 3056
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 754 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction754 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint9 =
      monsterCo1GeometryVectorPoint15 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint9.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint9_binary,
    monsterCo1GeometryVectorPoint15_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 5052430 6618096
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 755 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction755 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint10 =
      monsterCo1GeometryVectorPoint165 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint10.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint10_binary,
    monsterCo1GeometryVectorPoint165_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 5117966 6417392
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 756 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction756 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint11 =
      monsterCo1GeometryVectorPoint4 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint11.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint11_binary,
    monsterCo1GeometryVectorPoint4_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 7392240 5183502
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 757 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction757 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint12 =
      monsterCo1GeometryVectorPoint211 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint12.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint12_binary,
    monsterCo1GeometryVectorPoint211_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 4612096 4628480
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 758 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction758 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint13 =
      monsterCo1GeometryVectorPoint13 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint13.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint13_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 6866956 6866956
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 759 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction759 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint14 =
      monsterCo1GeometryVectorPoint212 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint14.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint14_binary,
    monsterCo1GeometryVectorPoint212_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 4201216 8374526
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 760 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction760 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint15 =
      monsterCo1GeometryVectorPoint9 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint15.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint15_binary,
    monsterCo1GeometryVectorPoint9_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 6618096 5052430
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 761 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction761 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint16 =
      monsterCo1GeometryVectorPoint20 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint16.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint16_binary,
    monsterCo1GeometryVectorPoint20_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 3146646 3176342
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 762 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction762 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint17 =
      monsterCo1GeometryVectorPoint213 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint17.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint17_binary,
    monsterCo1GeometryVectorPoint213_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 4614150 4841464
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 763 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction763 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint18 =
      monsterCo1GeometryVectorPoint22 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint18.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint18_binary,
    monsterCo1GeometryVectorPoint22_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 2423807 465234
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 764 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction764 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint19 =
      monsterCo1GeometryVectorPoint214 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint19.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint19_binary,
    monsterCo1GeometryVectorPoint214_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 403573 3362520
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 765 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction765 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint20 =
      monsterCo1GeometryVectorPoint16 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint20.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint20_binary,
    monsterCo1GeometryVectorPoint16_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 3176342 3146646
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 766 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction766 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint21 =
      monsterCo1GeometryVectorPoint215 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint21.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint21_binary,
    monsterCo1GeometryVectorPoint215_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 967170 1188657
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 767 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction767 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint22 =
      monsterCo1GeometryVectorPoint18 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint22.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint22_binary,
    monsterCo1GeometryVectorPoint18_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 465234 2423807
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

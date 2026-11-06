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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint023
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint024
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint029
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint034
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint044
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint078
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint079
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint099
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint171
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint172
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint173
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint174
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint175
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint176
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint177
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint178
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint179

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Binding 0 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction0 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint0 =
      monsterCo1GeometryVectorPoint1 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint0.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint0_binary,
    monsterCo1GeometryVectorPoint1_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 2048 4194304
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 1 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction1 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint1 =
      monsterCo1GeometryVectorPoint24 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint1.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint1_binary,
    monsterCo1GeometryVectorPoint24_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 4194304 4196352
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 2 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction2 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint2 =
      monsterCo1GeometryVectorPoint4 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint2.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint2_binary,
    monsterCo1GeometryVectorPoint4_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 5181440 5183502
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 3 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction3 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint3 =
      monsterCo1GeometryVectorPoint7 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint3.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint3_binary,
    monsterCo1GeometryVectorPoint7_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 4243456 4245516
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 4 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction4 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint4 =
      monsterCo1GeometryVectorPoint8 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint4.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint4_binary,
    monsterCo1GeometryVectorPoint8_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 5183502 985102
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 5 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction5 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint5 =
      monsterCo1GeometryVectorPoint29 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint5.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint5_binary,
    monsterCo1GeometryVectorPoint29_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 4587520 4589568
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 6 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction6 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint6 =
      monsterCo1GeometryVectorPoint171 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint6.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint6_binary,
    monsterCo1GeometryVectorPoint171_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 8372224 8374284
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 7 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction7 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint7 =
      monsterCo1GeometryVectorPoint34 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint7.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint7_binary,
    monsterCo1GeometryVectorPoint34_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 4245516 2060
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 8 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction8 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint8 =
      monsterCo1GeometryVectorPoint2 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint8.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint8_binary,
    monsterCo1GeometryVectorPoint2_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 985102 5181440
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 9 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction9 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint9 =
      monsterCo1GeometryVectorPoint78 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint9.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint9_binary,
    monsterCo1GeometryVectorPoint78_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 5052430 854030
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 10 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction10 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint10 =
      monsterCo1GeometryVectorPoint79 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint10.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint10_binary,
    monsterCo1GeometryVectorPoint79_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 5117966 919566
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 11 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction11 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint11 =
      monsterCo1GeometryVectorPoint172 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint11.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint11_binary,
    monsterCo1GeometryVectorPoint172_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 7392240 3197948
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 12 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction12 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint12 =
      monsterCo1GeometryVectorPoint17 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint12.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint12_binary,
    monsterCo1GeometryVectorPoint17_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 4612096 4614150
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 13 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction13 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint13 =
      monsterCo1GeometryVectorPoint44 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint13.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint13_binary,
    monsterCo1GeometryVectorPoint44_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 6866956 2623500
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 14 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction14 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint14 =
      monsterCo1GeometryVectorPoint173 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint14.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint14_binary,
    monsterCo1GeometryVectorPoint173_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 4201216 6926
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 15 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction15 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint15 =
      monsterCo1GeometryVectorPoint18 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint15.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint15_binary,
    monsterCo1GeometryVectorPoint18_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 6618096 2423807
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 16 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction16 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint16 =
      monsterCo1GeometryVectorPoint174 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint16.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint16_binary,
    monsterCo1GeometryVectorPoint174_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 3146646 3171216
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 17 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction17 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint17 =
      monsterCo1GeometryVectorPoint99 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint17.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint17_binary,
    monsterCo1GeometryVectorPoint99_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 4614150 395270
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 18 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction18 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint18 =
      monsterCo1GeometryVectorPoint175 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint18.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint18_binary,
    monsterCo1GeometryVectorPoint175_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 2423807 6554623
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 19 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction19 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint19 =
      monsterCo1GeometryVectorPoint176 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint19.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint19_binary,
    monsterCo1GeometryVectorPoint176_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 403573 4616317
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 20 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction20 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint20 =
      monsterCo1GeometryVectorPoint23 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint20.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint20_binary,
    monsterCo1GeometryVectorPoint23_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 3176342 11539352
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 21 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction21 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint21 =
      monsterCo1GeometryVectorPoint177 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint21.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint21_binary,
    monsterCo1GeometryVectorPoint177_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 967170 922124
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 22 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction22 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint22 =
      monsterCo1GeometryVectorPoint178 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint22.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint22_binary,
    monsterCo1GeometryVectorPoint178_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 465234 4702558
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 23 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction23 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint23 =
      monsterCo1GeometryVectorPoint179 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint23.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint23_binary,
    monsterCo1GeometryVectorPoint179_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 11539352 11560862
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

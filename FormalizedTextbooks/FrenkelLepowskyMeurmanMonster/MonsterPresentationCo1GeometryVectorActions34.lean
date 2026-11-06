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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint012
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint021
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint203
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint204
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint205
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint206
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint207
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint211
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint215
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint222
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint224
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint225
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint229
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint230
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint232
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint235
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint238
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint242
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint244
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint245
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint250
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint255
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint257
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint264
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint268
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint275
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint320
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint368
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint371
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint376
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint390
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint394
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint395
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint405
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint418
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint423
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint433
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint434
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint445
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint450
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint457
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint474
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint482
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint489
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint494
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint535
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint622

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Binding 816 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction816 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint203 =
      monsterCo1GeometryVectorPoint394 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint203.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint203_binary,
    monsterCo1GeometryVectorPoint394_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 28680 1032
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 817 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction817 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint204 =
      monsterCo1GeometryVectorPoint433 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint204.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint204_binary,
    monsterCo1GeometryVectorPoint433_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 748645 2636488
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 818 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction818 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint205 =
      monsterCo1GeometryVectorPoint535 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint205.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint205_binary,
    monsterCo1GeometryVectorPoint535_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 123936 2212928
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 819 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction819 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint206 =
      monsterCo1GeometryVectorPoint622 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint206.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint206_binary,
    monsterCo1GeometryVectorPoint622_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 6094731 8349990
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 820 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction820 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint207 =
      monsterCo1GeometryVectorPoint457 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint207.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint207_binary,
    monsterCo1GeometryVectorPoint457_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 568074 1589002
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 821 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction821 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint211 =
      monsterCo1GeometryVectorPoint12 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint211.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint211_binary,
    monsterCo1GeometryVectorPoint12_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 4628480 4612096
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 822 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction822 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint215 =
      monsterCo1GeometryVectorPoint21 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint215.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint215_binary,
    monsterCo1GeometryVectorPoint21_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 1188657 967170
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 823 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction823 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint222 =
      monsterCo1GeometryVectorPoint368 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint222.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint222_binary,
    monsterCo1GeometryVectorPoint368_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 7341040 5230606
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 824 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction824 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint224 =
      monsterCo1GeometryVectorPoint371 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint224.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint224_binary,
    monsterCo1GeometryVectorPoint371_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 4199318 4237206
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 825 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction825 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint225 =
      monsterCo1GeometryVectorPoint376 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint225.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint225_binary,
    monsterCo1GeometryVectorPoint376_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 5314560 6408192
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 826 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction826 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint229 =
      monsterCo1GeometryVectorPoint390 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint229.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint229_binary,
    monsterCo1GeometryVectorPoint390_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 746240 1200382
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 827 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction827 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint230 =
      monsterCo1GeometryVectorPoint395 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint230.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint230_binary,
    monsterCo1GeometryVectorPoint395_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 4616200 7787528
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 828 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction828 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint232 =
      monsterCo1GeometryVectorPoint405 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint232.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint232_binary,
    monsterCo1GeometryVectorPoint405_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 5716085 5410520
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 829 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction829 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint235 =
      monsterCo1GeometryVectorPoint418 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint235.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint235_binary,
    monsterCo1GeometryVectorPoint418_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 2910214 3485688
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 830 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction830 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint238 =
      monsterCo1GeometryVectorPoint423 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint238.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint238_binary,
    monsterCo1GeometryVectorPoint423_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 6279682 7594801
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 831 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction831 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint242 =
      monsterCo1GeometryVectorPoint434 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint242.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint242_binary,
    monsterCo1GeometryVectorPoint434_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 4945765 5763638
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 832 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction832 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint244 =
      monsterCo1GeometryVectorPoint445 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint244.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint244_binary,
    monsterCo1GeometryVectorPoint445_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 6779394 7041841
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 833 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction833 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint245 =
      monsterCo1GeometryVectorPoint450 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint245.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint245_binary,
    monsterCo1GeometryVectorPoint450_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 5249538 8137521
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 834 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction834 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint250 =
      monsterCo1GeometryVectorPoint250 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint250.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint250_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 400142 400142
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 835 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction835 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint255 =
      monsterCo1GeometryVectorPoint320 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint255.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint255_binary,
    monsterCo1GeometryVectorPoint320_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 1782771 524638
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 836 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction836 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint257 =
      monsterCo1GeometryVectorPoint474 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint257.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint257_binary,
    monsterCo1GeometryVectorPoint474_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 8179712 7995392
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 837 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction837 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint264 =
      monsterCo1GeometryVectorPoint482 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint264.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint264_binary,
    monsterCo1GeometryVectorPoint482_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 8181760 7997440
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 838 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction838 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint268 =
      monsterCo1GeometryVectorPoint489 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint268.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint268_binary,
    monsterCo1GeometryVectorPoint489_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 1100290 797489
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 839 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction839 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint275 =
      monsterCo1GeometryVectorPoint494 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint275.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint275_binary,
    monsterCo1GeometryVectorPoint494_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 4592534 7780246
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

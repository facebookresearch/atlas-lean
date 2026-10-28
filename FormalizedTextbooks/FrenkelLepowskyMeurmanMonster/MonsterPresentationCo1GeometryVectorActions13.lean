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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint010
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint025
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint029
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint199
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint699
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint704
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint705
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint755
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint767
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint772
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint777
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint779
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint780
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint783
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint791
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint808
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint815
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint821
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint824
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint826
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint829
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint830
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint835
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint838
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint844
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint848
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint849
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint850
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint851
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint852
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint854
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint855
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint858
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint859
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint861
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint863
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint865

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Binding 312 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction312 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint699 =
      monsterCo1GeometryVectorPoint826 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint699.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint699_binary,
    monsterCo1GeometryVectorPoint826_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 4287967 5834207
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 313 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction313 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint704 =
      monsterCo1GeometryVectorPoint829 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint704.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint704_binary,
    monsterCo1GeometryVectorPoint829_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 8639078 10205814
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 314 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction314 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint705 =
      monsterCo1GeometryVectorPoint830 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint705.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint705_binary,
    monsterCo1GeometryVectorPoint830_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 16235104 14406256
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 315 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction315 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint755 =
      monsterCo1GeometryVectorPoint844 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint755.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint755_binary,
    monsterCo1GeometryVectorPoint844_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 1555982 1646094
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 316 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction316 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint767 =
      monsterCo1GeometryVectorPoint848 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint767.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint767_binary,
    monsterCo1GeometryVectorPoint848_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 4083824 1990768
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 317 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction317 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint772 =
      monsterCo1GeometryVectorPoint199 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint772.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint772_binary,
    monsterCo1GeometryVectorPoint199_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 8879016 8747960
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 318 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction318 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint777 =
      monsterCo1GeometryVectorPoint850 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint777.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint777_binary,
    monsterCo1GeometryVectorPoint850_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 12259250 10817442
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 319 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction319 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint779 =
      monsterCo1GeometryVectorPoint849 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint779.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint779_binary,
    monsterCo1GeometryVectorPoint849_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 11287590 9976886
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 320 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction320 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint780 =
      monsterCo1GeometryVectorPoint851 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint780.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint780_binary,
    monsterCo1GeometryVectorPoint851_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 13487058 15989698
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 321 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction321 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint783 =
      monsterCo1GeometryVectorPoint852 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint783.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint783_binary,
    monsterCo1GeometryVectorPoint852_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 14436228 16170900
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 322 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction322 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint791 =
      monsterCo1GeometryVectorPoint855 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint791.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint791_binary,
    monsterCo1GeometryVectorPoint855_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 14532194 14409330
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 323 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction323 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint808 =
      monsterCo1GeometryVectorPoint859 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint808.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint808_binary,
    monsterCo1GeometryVectorPoint859_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 8526570 8526586
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 324 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction324 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint815 =
      monsterCo1GeometryVectorPoint861 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint815.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint815_binary,
    monsterCo1GeometryVectorPoint861_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 10439423 8602351
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 325 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction325 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint821 =
      monsterCo1GeometryVectorPoint863 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint821.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint821_binary,
    monsterCo1GeometryVectorPoint863_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 15316580 14407284
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 326 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction326 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint824 =
      monsterCo1GeometryVectorPoint865 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint824.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint824_binary,
    monsterCo1GeometryVectorPoint865_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 11600939 11469883
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 327 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction327 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint829 =
      monsterCo1GeometryVectorPoint704 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint829.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint829_binary,
    monsterCo1GeometryVectorPoint704_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 10205814 8639078
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 328 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction328 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint835 =
      monsterCo1GeometryVectorPoint858 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint835.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint835_binary,
    monsterCo1GeometryVectorPoint858_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 7529239 4229911
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 329 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction329 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint838 =
      monsterCo1GeometryVectorPoint854 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint838.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint838_binary,
    monsterCo1GeometryVectorPoint854_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 11968752 10879200
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 330 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction330 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint0 =
      monsterCo1GeometryVectorPoint0 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint0.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint0_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 2048 2048
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 331 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction331 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint1 =
      monsterCo1GeometryVectorPoint1 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint1.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint1_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 4194304 4194304
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 332 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction332 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint2 =
      monsterCo1GeometryVectorPoint25 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint2.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint2_binary,
    monsterCo1GeometryVectorPoint25_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 5181440 5183488
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 333 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction333 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint3 =
      monsterCo1GeometryVectorPoint3 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint3.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint3_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 4243456 4243456
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 334 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction334 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint4 =
      monsterCo1GeometryVectorPoint10 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint4.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint4_binary,
    monsterCo1GeometryVectorPoint10_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 5183502 5117966
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 335 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction335 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint5 =
      monsterCo1GeometryVectorPoint29 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint5.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint5_binary,
    monsterCo1GeometryVectorPoint29_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 4587520 4589568
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint752
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint754
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint758
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint764
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint767
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint770
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint772
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint773
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint790
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint833
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint842
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint843
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint845
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint846
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint847
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint848
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint849
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint851
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint862

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Binding 936 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction936 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint752 =
      monsterCo1GeometryVectorPoint752 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint752.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint752_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 422032 422032
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 937 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction937 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint754 =
      monsterCo1GeometryVectorPoint843 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint754.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint754_binary,
    monsterCo1GeometryVectorPoint843_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 11841872 10387459
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 938 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction938 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint758 =
      monsterCo1GeometryVectorPoint845 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint758.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint758_binary,
    monsterCo1GeometryVectorPoint845_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 16021852 14567439
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 939 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction939 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint764 =
      monsterCo1GeometryVectorPoint846 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint764.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint764_binary,
    monsterCo1GeometryVectorPoint846_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 8421408 8425536
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 940 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction940 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint767 =
      monsterCo1GeometryVectorPoint848 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint767.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint767_binary,
    monsterCo1GeometryVectorPoint848_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 4083824 1990768
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 941 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction941 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint770 =
      monsterCo1GeometryVectorPoint847 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint770.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint770_binary,
    monsterCo1GeometryVectorPoint847_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 14436418 16088028
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 942 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction942 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint772 =
      monsterCo1GeometryVectorPoint849 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint772.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint772_binary,
    monsterCo1GeometryVectorPoint849_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 8879016 9976886
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 943 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction943 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint773 =
      monsterCo1GeometryVectorPoint851 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint773.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint773_binary,
    monsterCo1GeometryVectorPoint851_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 15063970 15989698
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 944 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction944 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint790 =
      monsterCo1GeometryVectorPoint842 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint790.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint790_binary,
    monsterCo1GeometryVectorPoint842_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 15029201 13198050
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 945 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction945 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint833 =
      monsterCo1GeometryVectorPoint862 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint833.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint833_binary,
    monsterCo1GeometryVectorPoint862_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 8283876 5046313
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

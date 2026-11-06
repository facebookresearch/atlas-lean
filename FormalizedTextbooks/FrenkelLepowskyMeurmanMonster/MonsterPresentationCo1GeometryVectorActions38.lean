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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint326
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint435
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint436
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint543
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint550
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint565
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint566
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint572
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint578
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint579
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint582
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint606
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint611
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint616
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint653
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint654
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint655
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint656
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint669
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint673
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint674
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint677
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint678
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint685
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint716
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint721
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint744
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint747
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint749
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint753
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint756
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint757
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint759
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint760
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint765
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint768
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint780
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint805
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint806
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint810
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint811
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint812
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint813
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint817
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint836
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint839

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Binding 912 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction912 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint543 =
      monsterCo1GeometryVectorPoint673 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint543.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint543_binary,
    monsterCo1GeometryVectorPoint673_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 55822 3984189
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 913 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction913 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint550 =
      monsterCo1GeometryVectorPoint744 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint550.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint550_binary,
    monsterCo1GeometryVectorPoint744_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 2981604 3733545
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 914 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction914 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint565 =
      monsterCo1GeometryVectorPoint326 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint565.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint565_binary,
    monsterCo1GeometryVectorPoint326_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 7620608 4360192
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 915 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction915 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint566 =
      monsterCo1GeometryVectorPoint749 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint566.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint566_binary,
    monsterCo1GeometryVectorPoint749_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 7403870 5446643
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 916 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction916 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint572 =
      monsterCo1GeometryVectorPoint753 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint572.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint572_binary,
    monsterCo1GeometryVectorPoint753_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 1117169 1821346
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 917 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction917 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint578 =
      monsterCo1GeometryVectorPoint756 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint578.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint578_binary,
    monsterCo1GeometryVectorPoint756_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 4108292 1979396
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 918 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction918 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint579 =
      monsterCo1GeometryVectorPoint757 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint579.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint579_binary,
    monsterCo1GeometryVectorPoint757_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 7569415 7325012
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 919 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction919 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint582 =
      monsterCo1GeometryVectorPoint759 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint582.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint582_binary,
    monsterCo1GeometryVectorPoint759_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 8302596 6222852
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 920 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction920 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint606 =
      monsterCo1GeometryVectorPoint765 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint606.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint606_binary,
    monsterCo1GeometryVectorPoint765_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 16164866 13220860
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 921 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction921 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint611 =
      monsterCo1GeometryVectorPoint768 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint611.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint611_binary,
    monsterCo1GeometryVectorPoint768_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 1007720 988264
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 922 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction922 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint616 =
      monsterCo1GeometryVectorPoint780 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint616.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint616_binary,
    monsterCo1GeometryVectorPoint780_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 16505778 13487058
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 923 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction923 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint653 =
      monsterCo1GeometryVectorPoint805 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint653.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint653_binary,
    monsterCo1GeometryVectorPoint805_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 31246 817981
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 924 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction924 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint654 =
      monsterCo1GeometryVectorPoint806 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint654.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint654_binary,
    monsterCo1GeometryVectorPoint806_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 881152 1589453
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 925 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction925 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint655 =
      monsterCo1GeometryVectorPoint435 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint655.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint655_binary,
    monsterCo1GeometryVectorPoint435_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 2286397 971278
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 926 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction926 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint656 =
      monsterCo1GeometryVectorPoint436 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint656.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint656_binary,
    monsterCo1GeometryVectorPoint436_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 2287821 121344
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 927 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction927 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint669 =
      monsterCo1GeometryVectorPoint810 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint669.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint669_binary,
    monsterCo1GeometryVectorPoint810_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 6191882 6164234
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 928 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction928 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint674 =
      monsterCo1GeometryVectorPoint811 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint674.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint674_binary,
    monsterCo1GeometryVectorPoint811_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 2580196 1374249
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 929 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction929 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint677 =
      monsterCo1GeometryVectorPoint812 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint677.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint677_binary,
    monsterCo1GeometryVectorPoint812_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 5861642 8009671
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 930 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction930 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint678 =
      monsterCo1GeometryVectorPoint813 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint678.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint678_binary,
    monsterCo1GeometryVectorPoint813_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 8243466 5808071
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 931 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction931 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint685 =
      monsterCo1GeometryVectorPoint817 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint685.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint685_binary,
    monsterCo1GeometryVectorPoint817_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 7620324 6357033
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 932 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction932 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint716 =
      monsterCo1GeometryVectorPoint836 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint716.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint716_binary,
    monsterCo1GeometryVectorPoint836_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 1532170 1365959
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 933 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction933 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint721 =
      monsterCo1GeometryVectorPoint839 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint721.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint721_binary,
    monsterCo1GeometryVectorPoint839_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 5485372 4886690
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 934 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction934 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint747 =
      monsterCo1GeometryVectorPoint760 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint747.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint747_binary,
    monsterCo1GeometryVectorPoint760_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 7336284 5500943
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 935 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction935 :
    monsterCo1GeometryTransportOperator 14 • monsterCo1GeometryVectorPoint749 =
      monsterCo1GeometryVectorPoint566 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 14)
      monsterCo1GeometryVectorPoint749.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint749_binary,
    monsterCo1GeometryVectorPoint566_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 14) 5446643 7403870
    (monsterCo1GeometryBinaryOperatorMasks_decode 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

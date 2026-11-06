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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint537
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint541
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint542
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint545
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint561
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint584
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint605
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint613
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint615
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint621
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint622
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint627
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint631
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint633
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint634
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint639
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint647
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint648
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint686
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint687
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint703
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint722
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint725
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint728
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint737
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint739
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint740
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint742
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint745
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint747
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint761
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint764
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint769
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint773
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint782
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint786
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint789
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint790
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint793
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint794
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint795
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint799
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint800
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint818
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint819
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint822
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint828
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint840

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Binding 432 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction432 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint537 =
      monsterCo1GeometryVectorPoint728 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint537.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint537_binary,
    monsterCo1GeometryVectorPoint728_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 7144521 7447625
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 433 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction433 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint541 =
      monsterCo1GeometryVectorPoint739 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint541.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint541_binary,
    monsterCo1GeometryVectorPoint739_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 5155082 8044810
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 434 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction434 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint542 =
      monsterCo1GeometryVectorPoint740 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint542.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint542_binary,
    monsterCo1GeometryVectorPoint740_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 7020260 7782116
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 435 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction435 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint545 =
      monsterCo1GeometryVectorPoint742 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint545.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint545_binary,
    monsterCo1GeometryVectorPoint742_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 3191556 72452
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 436 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction436 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint561 =
      monsterCo1GeometryVectorPoint747 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint561.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint561_binary,
    monsterCo1GeometryVectorPoint747_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 4704604 7336284
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 437 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction437 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint584 =
      monsterCo1GeometryVectorPoint761 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint584.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint584_binary,
    monsterCo1GeometryVectorPoint761_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 1751752 1252040
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 438 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction438 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint605 =
      monsterCo1GeometryVectorPoint764 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint605.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint605_binary,
    monsterCo1GeometryVectorPoint764_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 8417280 8421408
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 439 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction439 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint613 =
      monsterCo1GeometryVectorPoint769 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint613.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint613_binary,
    monsterCo1GeometryVectorPoint769_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 1015263 2328031
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 440 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction440 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint615 =
      monsterCo1GeometryVectorPoint773 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint615.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint615_binary,
    monsterCo1GeometryVectorPoint773_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 15221634 15063970
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 441 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction441 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint621 =
      monsterCo1GeometryVectorPoint786 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint621.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint621_binary,
    monsterCo1GeometryVectorPoint786_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 3270726 2967622
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 442 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction442 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint622 =
      monsterCo1GeometryVectorPoint782 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint622.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint622_binary,
    monsterCo1GeometryVectorPoint782_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 8349990 6226214
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 443 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction443 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint627 =
      monsterCo1GeometryVectorPoint789 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint627.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint627_binary,
    monsterCo1GeometryVectorPoint789_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 12020706 9067458
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 444 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction444 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint631 =
      monsterCo1GeometryVectorPoint790 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint631.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint631_binary,
    monsterCo1GeometryVectorPoint790_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 13409265 15029201
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 445 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction445 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint633 =
      monsterCo1GeometryVectorPoint793 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint633.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint633_binary,
    monsterCo1GeometryVectorPoint793_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 5695255 7583511
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 446 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction446 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint634 =
      monsterCo1GeometryVectorPoint794 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint634.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint634_binary,
    monsterCo1GeometryVectorPoint794_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 2529047 247575
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 447 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction447 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint639 =
      monsterCo1GeometryVectorPoint745 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint639.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint639_binary,
    monsterCo1GeometryVectorPoint745_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 6146314 6924554
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 448 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction448 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint647 =
      monsterCo1GeometryVectorPoint799 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint647.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint647_binary,
    monsterCo1GeometryVectorPoint799_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 15894424 13100984
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 449 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction449 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint648 =
      monsterCo1GeometryVectorPoint800 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint648.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint648_binary,
    monsterCo1GeometryVectorPoint800_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 7318070 4690486
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 450 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction450 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint686 =
      monsterCo1GeometryVectorPoint818 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint686.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint686_binary,
    monsterCo1GeometryVectorPoint818_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 6180440 4709976
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 451 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction451 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint687 =
      monsterCo1GeometryVectorPoint819 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint687.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint687_binary,
    monsterCo1GeometryVectorPoint819_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 1007192 1494616
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 452 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction452 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint703 =
      monsterCo1GeometryVectorPoint828 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint703.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint703_binary,
    monsterCo1GeometryVectorPoint828_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 1988324 259812
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 453 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction453 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint722 =
      monsterCo1GeometryVectorPoint840 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint722.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint722_binary,
    monsterCo1GeometryVectorPoint840_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 4931116 6026796
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 454 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction454 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint725 =
      monsterCo1GeometryVectorPoint822 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint725.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint725_binary,
    monsterCo1GeometryVectorPoint822_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 7362015 6071775
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 455 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction455 :
    monsterCo1GeometryTransportOperator 6 • monsterCo1GeometryVectorPoint737 =
      monsterCo1GeometryVectorPoint795 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 6)
      monsterCo1GeometryVectorPoint737.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint737_binary,
    monsterCo1GeometryVectorPoint795_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 6) 2019852 924172
    (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

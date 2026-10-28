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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint460
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint469
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint480
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint488
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint493
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint498
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint505
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint512
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint514
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint520
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint521
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint528
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint529
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint532
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint533
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint534
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint542
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint548
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint600
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint618
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint632
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint643
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint655
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint656
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint671
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint695
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint696
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint698
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint701
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint706
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint710
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint711
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint716
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint720
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint721
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint727
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint730
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint731
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint732
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint743
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint784
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint792
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint798
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint805
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint806
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint810
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint825

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Binding 288 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction288 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint460 =
      monsterCo1GeometryVectorPoint542 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint460.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint460_binary,
    monsterCo1GeometryVectorPoint542_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 6942436 7020260
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 289 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction289 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint469 =
      monsterCo1GeometryVectorPoint469 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint469.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint469_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 4387737 4387737
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 290 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction290 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint480 =
      monsterCo1GeometryVectorPoint696 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint480.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint480_binary,
    monsterCo1GeometryVectorPoint696_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 3282931 927731
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 291 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction291 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint488 =
      monsterCo1GeometryVectorPoint701 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint488.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint488_binary,
    monsterCo1GeometryVectorPoint701_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 4624267 7112587
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 292 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction292 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint493 =
      monsterCo1GeometryVectorPoint706 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint493.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint493_binary,
    monsterCo1GeometryVectorPoint706_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 4020341 90229
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 293 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction293 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint498 =
      monsterCo1GeometryVectorPoint600 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint498.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint498_binary,
    monsterCo1GeometryVectorPoint600_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 2958344 1778696
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 294 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction294 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint505 =
      monsterCo1GeometryVectorPoint711 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint505.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint505_binary,
    monsterCo1GeometryVectorPoint711_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 6417096 4975304
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 295 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction295 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint512 =
      monsterCo1GeometryVectorPoint710 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint512.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint512_binary,
    monsterCo1GeometryVectorPoint710_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 68362 1663754
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 296 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction296 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint514 =
      monsterCo1GeometryVectorPoint716 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint514.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint514_binary,
    monsterCo1GeometryVectorPoint716_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 239882 1532170
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 297 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction297 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint520 =
      monsterCo1GeometryVectorPoint720 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint520.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint520_binary,
    monsterCo1GeometryVectorPoint720_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 3743498 2193162
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 298 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction298 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint521 =
      monsterCo1GeometryVectorPoint721 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint521.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint521_binary,
    monsterCo1GeometryVectorPoint721_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 8334140 5485372
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 299 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction299 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint528 =
      monsterCo1GeometryVectorPoint727 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint528.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint528_binary,
    monsterCo1GeometryVectorPoint727_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 1362976 1326112
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 300 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction300 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint529 =
      monsterCo1GeometryVectorPoint695 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint529.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint529_binary,
    monsterCo1GeometryVectorPoint695_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 1430560 1387552
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 301 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction301 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint532 =
      monsterCo1GeometryVectorPoint730 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint532.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint532_binary,
    monsterCo1GeometryVectorPoint730_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 8511521 8642609
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 302 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction302 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint533 =
      monsterCo1GeometryVectorPoint731 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint533.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint533_binary,
    monsterCo1GeometryVectorPoint731_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 1777119 226783
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 303 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction303 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint534 =
      monsterCo1GeometryVectorPoint732 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint534.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint534_binary,
    monsterCo1GeometryVectorPoint732_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 5574111 5072351
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 304 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction304 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint548 =
      monsterCo1GeometryVectorPoint743 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint548.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint548_binary,
    monsterCo1GeometryVectorPoint743_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 4897034 6191370
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 305 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction305 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint618 =
      monsterCo1GeometryVectorPoint784 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint618.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint618_binary,
    monsterCo1GeometryVectorPoint784_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 10271631 11029407
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 306 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction306 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint632 =
      monsterCo1GeometryVectorPoint792 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint632.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint632_binary,
    monsterCo1GeometryVectorPoint792_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 14537318 12958326
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 307 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction307 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint643 =
      monsterCo1GeometryVectorPoint798 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint643.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint643_binary,
    monsterCo1GeometryVectorPoint798_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 13327459 12817523
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 308 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction308 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint655 =
      monsterCo1GeometryVectorPoint805 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint655.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint655_binary,
    monsterCo1GeometryVectorPoint805_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 2286397 817981
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 309 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction309 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint656 =
      monsterCo1GeometryVectorPoint806 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint656.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint656_binary,
    monsterCo1GeometryVectorPoint806_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 2287821 1589453
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 310 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction310 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint671 =
      monsterCo1GeometryVectorPoint810 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint671.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint671_binary,
    monsterCo1GeometryVectorPoint810_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 4615946 6164234
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 311 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction311 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint698 =
      monsterCo1GeometryVectorPoint825 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint698.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint698_binary,
    monsterCo1GeometryVectorPoint825_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 11616299 11485243
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

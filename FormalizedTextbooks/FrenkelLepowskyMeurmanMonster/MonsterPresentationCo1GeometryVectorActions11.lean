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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint175
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint352
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint375
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint376
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint377
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint378
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint389
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint394
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint400
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint401
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint405
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint406
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint414
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint416
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint422
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint425
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint429
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint431
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint433
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint435
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint436
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint440
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint448
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint455
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint456
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint457
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint458
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint476
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint501
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint546
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint594
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint604
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint609
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint610
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint612
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint615
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint627
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint642
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint644
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint653
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint654
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint657
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint669
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint675
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint676
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint677
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint683

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Binding 264 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction264 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint375 =
      monsterCo1GeometryVectorPoint376 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint375.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint375_binary,
    monsterCo1GeometryVectorPoint376_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 6406144 6408192
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 265 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction265 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint377 =
      monsterCo1GeometryVectorPoint594 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint377.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint377_binary,
    monsterCo1GeometryVectorPoint594_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 4630538 5941258
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 266 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction266 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint378 =
      monsterCo1GeometryVectorPoint378 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint378.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint378_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 7213056 7213056
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 267 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction267 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint389 =
      monsterCo1GeometryVectorPoint476 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint389.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint389_binary,
    monsterCo1GeometryVectorPoint476_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 5994504 7174152
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 268 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction268 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint394 =
      monsterCo1GeometryVectorPoint604 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint394.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint394_binary,
    monsterCo1GeometryVectorPoint604_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 1032 3542024
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 269 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction269 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint400 =
      monsterCo1GeometryVectorPoint609 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint400.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint400_binary,
    monsterCo1GeometryVectorPoint609_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 848503 1469047
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 270 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction270 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint401 =
      monsterCo1GeometryVectorPoint610 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint401.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint401_binary,
    monsterCo1GeometryVectorPoint610_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 143477 4063349
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 271 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction271 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint405 =
      monsterCo1GeometryVectorPoint612 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint405.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint405_binary,
    monsterCo1GeometryVectorPoint612_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 5410520 7898840
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 272 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction272 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint406 =
      monsterCo1GeometryVectorPoint615 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint406.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint406_binary,
    monsterCo1GeometryVectorPoint615_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 16169874 15221634
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 273 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction273 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint414 =
      monsterCo1GeometryVectorPoint627 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint414.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint414_binary,
    monsterCo1GeometryVectorPoint627_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 9022450 12020706
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 274 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction274 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint416 =
      monsterCo1GeometryVectorPoint501 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint416.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint416_binary,
    monsterCo1GeometryVectorPoint501_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 1928804 3145316
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 275 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction275 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint422 =
      monsterCo1GeometryVectorPoint546 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint422.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint422_binary,
    monsterCo1GeometryVectorPoint546_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 3742474 2192138
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 276 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction276 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint425 =
      monsterCo1GeometryVectorPoint175 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint425.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint425_binary,
    monsterCo1GeometryVectorPoint175_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 7353343 6554623
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 277 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction277 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint429 =
      monsterCo1GeometryVectorPoint644 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint429.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint429_binary,
    monsterCo1GeometryVectorPoint644_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 13316198 14678134
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 278 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction278 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint431 =
      monsterCo1GeometryVectorPoint352 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint431.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint431_binary,
    monsterCo1GeometryVectorPoint352_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 246885 4193381
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 279 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction279 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint433 =
      monsterCo1GeometryVectorPoint642 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint433.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint433_binary,
    monsterCo1GeometryVectorPoint642_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 2636488 144072
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 280 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction280 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint435 =
      monsterCo1GeometryVectorPoint653 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint435.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint435_binary,
    monsterCo1GeometryVectorPoint653_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 971278 31246
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 281 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction281 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint436 =
      monsterCo1GeometryVectorPoint654 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint436.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint436_binary,
    monsterCo1GeometryVectorPoint654_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 121344 881152
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 282 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction282 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint440 =
      monsterCo1GeometryVectorPoint657 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint440.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint440_binary,
    monsterCo1GeometryVectorPoint657_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 3006657 4145345
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 283 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction283 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint448 =
      monsterCo1GeometryVectorPoint669 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint448.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint448_binary,
    monsterCo1GeometryVectorPoint669_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 4594442 6191882
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 284 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction284 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint455 =
      monsterCo1GeometryVectorPoint676 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint455.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint455_binary,
    monsterCo1GeometryVectorPoint676_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 4827402 6119690
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 285 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction285 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint456 =
      monsterCo1GeometryVectorPoint677 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint456.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint456_binary,
    monsterCo1GeometryVectorPoint677_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 5093642 5861642
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 286 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction286 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint457 =
      monsterCo1GeometryVectorPoint675 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint457.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint457_binary,
    monsterCo1GeometryVectorPoint675_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 1589002 24330
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 287 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction287 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint458 =
      monsterCo1GeometryVectorPoint683 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint458.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint458_binary,
    monsterCo1GeometryVectorPoint683_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 1229629 3955517
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

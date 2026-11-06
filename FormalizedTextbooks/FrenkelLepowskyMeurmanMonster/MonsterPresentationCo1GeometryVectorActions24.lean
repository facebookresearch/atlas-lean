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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint221
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint222
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint223
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint224
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint225
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint226
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint227
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint228
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint229
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint231
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint232
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint233
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint234
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint236
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint237
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint238
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint239
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint244
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint246
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint247
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint248
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint249
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint251
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint253
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint295
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint360
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint366
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint369
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint370
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint374
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint379
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint382
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint384
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint389
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint393
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint401
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint404
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint408
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint417
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint419
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint422
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint424
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint443
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint456
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint461
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint465
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint466
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint470

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Binding 576 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction576 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint221 =
      monsterCo1GeometryVectorPoint360 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint221.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint221_binary,
    monsterCo1GeometryVectorPoint360_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 1190896 58262
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 577 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction577 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint222 =
      monsterCo1GeometryVectorPoint366 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint222.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint222_binary,
    monsterCo1GeometryVectorPoint366_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 7341040 986006
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 578 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction578 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint223 =
      monsterCo1GeometryVectorPoint369 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint223.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint223_binary,
    monsterCo1GeometryVectorPoint369_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 1588208 62358
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 579 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction579 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint224 =
      monsterCo1GeometryVectorPoint370 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint224.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint224_binary,
    monsterCo1GeometryVectorPoint370_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 4199318 7755893
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 580 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction580 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint225 =
      monsterCo1GeometryVectorPoint374 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint225.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint225_binary,
    monsterCo1GeometryVectorPoint374_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 5314560 3258368
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 581 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction581 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint226 =
      monsterCo1GeometryVectorPoint379 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint226.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint226_binary,
    monsterCo1GeometryVectorPoint379_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 4630528 7215104
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 582 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction582 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint227 =
      monsterCo1GeometryVectorPoint382 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint227.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint227_binary,
    monsterCo1GeometryVectorPoint382_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 248576 4026376
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 583 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction583 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint228 =
      monsterCo1GeometryVectorPoint384 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint228.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint228_binary,
    monsterCo1GeometryVectorPoint384_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 3984128 720904
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 584 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction584 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint229 =
      monsterCo1GeometryVectorPoint389 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint229.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint229_binary,
    monsterCo1GeometryVectorPoint389_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 746240 5994504
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 585 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction585 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint231 =
      monsterCo1GeometryVectorPoint401 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint231.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint231_binary,
    monsterCo1GeometryVectorPoint401_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 7736214 143477
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 586 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction586 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint232 =
      monsterCo1GeometryVectorPoint404 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint232.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint232_binary,
    monsterCo1GeometryVectorPoint404_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 5716085 3167264
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 587 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction587 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint233 =
      monsterCo1GeometryVectorPoint408 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint233.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint233_binary,
    monsterCo1GeometryVectorPoint408_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 7788438 3338123
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 588 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction588 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint234 =
      monsterCo1GeometryVectorPoint417 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint234.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint234_binary,
    monsterCo1GeometryVectorPoint417_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 598008 7175780
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 589 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction589 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint236 =
      monsterCo1GeometryVectorPoint419 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint236.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint236_binary,
    monsterCo1GeometryVectorPoint419_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 3409926 2597378
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 590 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction590 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint237 =
      monsterCo1GeometryVectorPoint295 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint237.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint237_binary,
    monsterCo1GeometryVectorPoint295_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 2885638 1774082
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 591 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction591 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint238 =
      monsterCo1GeometryVectorPoint422 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint238.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint238_binary,
    monsterCo1GeometryVectorPoint422_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 6279682 3742474
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 592 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction592 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint239 =
      monsterCo1GeometryVectorPoint424 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint239.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint239_binary,
    monsterCo1GeometryVectorPoint424_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 1015800 7568996
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 593 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction593 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint244 =
      monsterCo1GeometryVectorPoint443 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint244.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint244_binary,
    monsterCo1GeometryVectorPoint443_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 6779394 7301898
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 594 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction594 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint246 =
      monsterCo1GeometryVectorPoint456 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint246.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint246_binary,
    monsterCo1GeometryVectorPoint456_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 5155594 5093642
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 595 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction595 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint247 =
      monsterCo1GeometryVectorPoint461 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint247.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint247_binary,
    monsterCo1GeometryVectorPoint461_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 7201585 3116772
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 596 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction596 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint248 =
      monsterCo1GeometryVectorPoint465 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint248.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint248_binary,
    monsterCo1GeometryVectorPoint465_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 1708032 3186688
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 597 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction597 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint249 =
      monsterCo1GeometryVectorPoint466 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint249.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint249_binary,
    monsterCo1GeometryVectorPoint466_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 7385088 1732608
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 598 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction598 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint251 =
      monsterCo1GeometryVectorPoint393 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint251.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint251_binary,
    monsterCo1GeometryVectorPoint393_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 5157632 2979848
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 599 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction599 :
    monsterCo1GeometryTransportOperator 13 • monsterCo1GeometryVectorPoint253 =
      monsterCo1GeometryVectorPoint470 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 13)
      monsterCo1GeometryVectorPoint253.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint253_binary,
    monsterCo1GeometryVectorPoint470_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 13) 170902 1273973
    (monsterCo1GeometryBinaryOperatorMasks_decode 13)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

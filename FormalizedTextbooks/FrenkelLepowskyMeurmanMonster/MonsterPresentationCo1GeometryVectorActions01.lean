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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint040
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint048
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint052
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint053
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint065
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint069
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint089
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint090
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint094
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint122
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint130
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint131
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint135
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint144
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint145
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint147
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint151
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint157
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint158
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint159
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint161
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint163
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint164
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint167
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint222
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint231
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint240
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint243
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint250
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint255
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint260
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint262
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint265
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint287
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint293
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint298
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint308
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint320
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint321
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint322
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint327
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint331
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint332
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint334
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint336
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint339
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint340
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint343

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Binding 24 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction24 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint40 =
      monsterCo1GeometryVectorPoint222 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint40.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint40_binary,
    monsterCo1GeometryVectorPoint222_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 3148784 7341040
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 25 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction25 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint48 =
      monsterCo1GeometryVectorPoint231 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint48.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint48_binary,
    monsterCo1GeometryVectorPoint231_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 7758742 7736214
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 26 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction26 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint52 =
      monsterCo1GeometryVectorPoint240 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint52.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint52_binary,
    monsterCo1GeometryVectorPoint240_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 6566899 6556659
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 27 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction27 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint53 =
      monsterCo1GeometryVectorPoint243 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint53.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint53_binary,
    monsterCo1GeometryVectorPoint243_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 4313602 4262402
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 28 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction28 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint65 =
      monsterCo1GeometryVectorPoint250 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint65.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint65_binary,
    monsterCo1GeometryVectorPoint250_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 4594432 400142
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 29 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction29 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint69 =
      monsterCo1GeometryVectorPoint255 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint69.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint69_binary,
    monsterCo1GeometryVectorPoint255_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 1782768 1782771
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 30 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction30 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint89 =
      monsterCo1GeometryVectorPoint260 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint89.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint89_binary,
    monsterCo1GeometryVectorPoint260_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 5227504 5229564
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 31 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction31 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint90 =
      monsterCo1GeometryVectorPoint262 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint90.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint90_binary,
    monsterCo1GeometryVectorPoint262_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 7073792 7075855
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 32 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction32 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint94 =
      monsterCo1GeometryVectorPoint265 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint94.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint94_binary,
    monsterCo1GeometryVectorPoint265_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 592640 4784896
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 33 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction33 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint122 =
      monsterCo1GeometryVectorPoint287 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint122.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint122_binary,
    monsterCo1GeometryVectorPoint287_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 7076863 2821119
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 34 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction34 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint130 =
      monsterCo1GeometryVectorPoint293 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint130.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint130_binary,
    monsterCo1GeometryVectorPoint293_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 709122 655874
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 35 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction35 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint131 =
      monsterCo1GeometryVectorPoint298 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint131.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint131_binary,
    monsterCo1GeometryVectorPoint298_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 4571650 4528652
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 36 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction36 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint135 =
      monsterCo1GeometryVectorPoint308 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint135.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint135_binary,
    monsterCo1GeometryVectorPoint308_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 4243970 4200972
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 37 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction37 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint144 =
      monsterCo1GeometryVectorPoint320 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint144.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint144_binary,
    monsterCo1GeometryVectorPoint320_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 528734 524638
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 38 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction38 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint145 =
      monsterCo1GeometryVectorPoint321 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint145.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint145_binary,
    monsterCo1GeometryVectorPoint321_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 2371584 2371587
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 39 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction39 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint147 =
      monsterCo1GeometryVectorPoint322 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint147.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint147_binary,
    monsterCo1GeometryVectorPoint322_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 6025216 6027279
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 40 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction40 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint151 =
      monsterCo1GeometryVectorPoint327 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint151.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint151_binary,
    monsterCo1GeometryVectorPoint327_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 858450 5095774
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 41 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction41 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint157 =
      monsterCo1GeometryVectorPoint331 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint157.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint157_binary,
    monsterCo1GeometryVectorPoint331_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 4578288 383986
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 42 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction42 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint158 =
      monsterCo1GeometryVectorPoint332 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint158.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint158_binary,
    monsterCo1GeometryVectorPoint332_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 1125360 5317629
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 43 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction43 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint159 =
      monsterCo1GeometryVectorPoint334 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint159.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint159_binary,
    monsterCo1GeometryVectorPoint334_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 8049648 8051698
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 44 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction44 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint161 =
      monsterCo1GeometryVectorPoint336 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint161.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint161_binary,
    monsterCo1GeometryVectorPoint336_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 7721968 7724018
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 45 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction45 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint163 =
      monsterCo1GeometryVectorPoint339 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint163.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint163_binary,
    monsterCo1GeometryVectorPoint339_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 5366768 5368817
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 46 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction46 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint164 =
      monsterCo1GeometryVectorPoint340 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint164.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint164_binary,
    monsterCo1GeometryVectorPoint340_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 332784 332798
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 47 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction47 :
    monsterCo1GeometryTransportOperator 0 • monsterCo1GeometryVectorPoint167 =
      monsterCo1GeometryVectorPoint343 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 0)
      monsterCo1GeometryVectorPoint167.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint167_binary,
    monsterCo1GeometryVectorPoint343_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) 1998848 1998855
    (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

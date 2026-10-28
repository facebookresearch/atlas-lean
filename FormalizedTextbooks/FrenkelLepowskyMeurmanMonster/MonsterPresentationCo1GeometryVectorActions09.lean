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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint023
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint053
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint099
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint117
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint118
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint130
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint133
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint135
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint137
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint172
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint174
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint175
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint176
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint186
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint190
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint193
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint199
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint200
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint201
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint202
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint203
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint204
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint206
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint207
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint214
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint215
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint225
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint244
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint273
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint283
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint285
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint294
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint302
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint309
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint312
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint363
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint392
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint399
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint409
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint425
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint428
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint444
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint452
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint522
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint526
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint619
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint772

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Binding 216 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction216 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint53 =
      monsterCo1GeometryVectorPoint244 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint53.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint53_binary,
    monsterCo1GeometryVectorPoint244_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 4313602 6779394
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 217 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction217 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint99 =
      monsterCo1GeometryVectorPoint273 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint99.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint99_binary,
    monsterCo1GeometryVectorPoint273_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 395270 3278854
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 218 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction218 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint117 =
      monsterCo1GeometryVectorPoint283 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint117.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint117_binary,
    monsterCo1GeometryVectorPoint283_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 4941830 8347654
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 219 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction219 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint118 =
      monsterCo1GeometryVectorPoint285 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint118.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint118_binary,
    monsterCo1GeometryVectorPoint285_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 854022 3735558
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 220 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction220 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint130 =
      monsterCo1GeometryVectorPoint294 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint130.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint130_binary,
    monsterCo1GeometryVectorPoint294_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 709122 2914818
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 221 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction221 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint133 =
      monsterCo1GeometryVectorPoint302 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint133.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint133_binary,
    monsterCo1GeometryVectorPoint302_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 5056629 7409781
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 222 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction222 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint135 =
      monsterCo1GeometryVectorPoint309 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint135.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint135_binary,
    monsterCo1GeometryVectorPoint309_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 4243970 6711810
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 223 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction223 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint137 =
      monsterCo1GeometryVectorPoint312 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint137.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint137_binary,
    monsterCo1GeometryVectorPoint312_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 770562 2974210
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 224 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction224 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint172 =
      monsterCo1GeometryVectorPoint363 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint172.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint172_binary,
    monsterCo1GeometryVectorPoint363_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 3197948 850940
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 225 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction225 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint174 =
      monsterCo1GeometryVectorPoint399 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint174.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint174_binary,
    monsterCo1GeometryVectorPoint399_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 3171216 287632
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 226 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction226 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint175 =
      monsterCo1GeometryVectorPoint425 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint175.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint175_binary,
    monsterCo1GeometryVectorPoint425_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 6554623 7353343
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 227 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction227 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint176 =
      monsterCo1GeometryVectorPoint522 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint176.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint176_binary,
    monsterCo1GeometryVectorPoint522_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 4616317 4999293
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 228 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction228 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint186 =
      monsterCo1GeometryVectorPoint23 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint186.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint186_binary,
    monsterCo1GeometryVectorPoint23_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 11725704 11539352
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 229 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction229 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint190 =
      monsterCo1GeometryVectorPoint202 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint190.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint190_binary,
    monsterCo1GeometryVectorPoint202_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 4766464 5036800
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 230 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction230 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint193 =
      monsterCo1GeometryVectorPoint409 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint193.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint193_binary,
    monsterCo1GeometryVectorPoint409_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 6971398 6184966
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 231 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction231 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint199 =
      monsterCo1GeometryVectorPoint772 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint199.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint199_binary,
    monsterCo1GeometryVectorPoint772_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 8747960 8879016
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 232 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction232 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint200 =
      monsterCo1GeometryVectorPoint200 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint200.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint200_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 7344128 7344128
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 233 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction233 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint201 =
      monsterCo1GeometryVectorPoint225 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint201.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint201_binary,
    monsterCo1GeometryVectorPoint225_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 5312512 5314560
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 234 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction234 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint203 =
      monsterCo1GeometryVectorPoint392 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint203.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint203_binary,
    monsterCo1GeometryVectorPoint392_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 28680 3569672
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 235 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction235 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint204 =
      monsterCo1GeometryVectorPoint428 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint204.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint204_binary,
    monsterCo1GeometryVectorPoint428_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 748645 3626085
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 236 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction236 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint206 =
      monsterCo1GeometryVectorPoint619 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint206.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint206_binary,
    monsterCo1GeometryVectorPoint619_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 6094731 7796619
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 237 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction237 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint207 =
      monsterCo1GeometryVectorPoint452 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint207.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint207_binary,
    monsterCo1GeometryVectorPoint452_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 568074 1100554
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 238 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction238 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint214 =
      monsterCo1GeometryVectorPoint526 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint214.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint214_binary,
    monsterCo1GeometryVectorPoint526_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 3362520 1658584
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 239 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction239 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint215 =
      monsterCo1GeometryVectorPoint444 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint215.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint215_binary,
    monsterCo1GeometryVectorPoint444_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 1188657 1358641
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

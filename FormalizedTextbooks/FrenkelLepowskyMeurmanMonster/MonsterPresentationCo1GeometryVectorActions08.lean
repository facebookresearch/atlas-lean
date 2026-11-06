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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint003
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint004
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint005
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint006
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint007
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint008
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint009
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint010
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint011
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint012
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint013
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint014
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint015
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint016
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint017
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint018
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint019
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint020
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint021
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint022
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint023
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint032
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint046
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint051
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint052
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint078
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint106
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint180
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint181
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint182
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint183
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint184
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint185
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint186
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint229
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint236
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint241

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Binding 192 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction192 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint3 =
      monsterCo1GeometryVectorPoint3 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint3.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint3_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 4243456 4243456
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 193 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction193 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint4 =
      monsterCo1GeometryVectorPoint9 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint4.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint4_binary,
    monsterCo1GeometryVectorPoint9_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 5183502 5052430
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 194 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction194 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint5 =
      monsterCo1GeometryVectorPoint5 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint5.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint5_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 4587520 4587520
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 195 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction195 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint6 =
      monsterCo1GeometryVectorPoint32 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint6.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint6_binary,
    monsterCo1GeometryVectorPoint32_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 8372224 8374272
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 196 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction196 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint7 =
      monsterCo1GeometryVectorPoint13 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint7.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint7_binary,
    monsterCo1GeometryVectorPoint13_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 4245516 6866956
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 197 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction197 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint8 =
      monsterCo1GeometryVectorPoint78 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint8.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint8_binary,
    monsterCo1GeometryVectorPoint78_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 985102 854030
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 198 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction198 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint9 =
      monsterCo1GeometryVectorPoint4 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint9.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint9_binary,
    monsterCo1GeometryVectorPoint4_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 5052430 5183502
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 199 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction199 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint10 =
      monsterCo1GeometryVectorPoint106 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint10.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint10_binary,
    monsterCo1GeometryVectorPoint106_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 5117966 4984846
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 200 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction200 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint11 =
      monsterCo1GeometryVectorPoint15 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint11.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint11_binary,
    monsterCo1GeometryVectorPoint15_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 7392240 6618096
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 201 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction201 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint12 =
      monsterCo1GeometryVectorPoint12 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint12.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint12_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 4612096 4612096
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 202 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction202 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint13 =
      monsterCo1GeometryVectorPoint7 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint13.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint13_binary,
    monsterCo1GeometryVectorPoint7_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 6866956 4245516
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 203 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction203 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint14 =
      monsterCo1GeometryVectorPoint180 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint14.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint14_binary,
    monsterCo1GeometryVectorPoint180_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 4201216 4487936
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 204 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction204 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint15 =
      monsterCo1GeometryVectorPoint11 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint15.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint15_binary,
    monsterCo1GeometryVectorPoint11_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 6618096 7392240
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 205 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction205 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint16 =
      monsterCo1GeometryVectorPoint16 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint16.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint16_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 3146646 3146646
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 206 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction206 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint17 =
      monsterCo1GeometryVectorPoint181 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint17.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint17_binary,
    monsterCo1GeometryVectorPoint181_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 4614150 7497734
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 207 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction207 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint18 =
      monsterCo1GeometryVectorPoint182 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint18.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint18_binary,
    monsterCo1GeometryVectorPoint182_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 2423807 3197951
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 208 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction208 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint19 =
      monsterCo1GeometryVectorPoint183 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint19.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint19_binary,
    monsterCo1GeometryVectorPoint183_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 403573 3807349
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 209 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction209 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint20 =
      monsterCo1GeometryVectorPoint20 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint20.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint20_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 3176342 3176342
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 210 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction210 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint21 =
      monsterCo1GeometryVectorPoint184 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint21.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint21_binary,
    monsterCo1GeometryVectorPoint184_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 967170 2648578
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 211 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction211 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint22 =
      monsterCo1GeometryVectorPoint185 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint22.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint22_binary,
    monsterCo1GeometryVectorPoint185_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 465234 334162
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 212 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction212 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint23 =
      monsterCo1GeometryVectorPoint186 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint23.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint23_binary,
    monsterCo1GeometryVectorPoint186_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 11539352 11725704
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 213 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction213 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint46 =
      monsterCo1GeometryVectorPoint229 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint46.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint46_binary,
    monsterCo1GeometryVectorPoint229_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 985856 746240
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 214 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction214 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint51 =
      monsterCo1GeometryVectorPoint236 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint51.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint51_binary,
    monsterCo1GeometryVectorPoint236_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 2054 3409926
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Binding 215 retains the actual Conway operator image of the literal source point. -/
theorem monsterCo1GeometryVectorAction215 :
    monsterCo1GeometryTransportOperator 5 • monsterCo1GeometryVectorPoint52 =
      monsterCo1GeometryVectorPoint241 := by
  apply Subtype.ext
  change co1BinaryAction (monsterCo1GeometryTransportOperator 5)
      monsterCo1GeometryVectorPoint52.val = _
  rw [monsterCo1GeometryTransportOperator_binary, monsterCo1GeometryVectorPoint52_binary,
    monsterCo1GeometryVectorPoint241_binary]
  exact monsterCo1GeometryBinaryMaskVector_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 5) 6566899 5768179
    (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

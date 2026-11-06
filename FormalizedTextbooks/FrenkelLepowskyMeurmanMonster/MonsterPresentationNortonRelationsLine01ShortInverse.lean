/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- All complete actual inverse Norton short images needed by the first line-pair word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ShortInverseBatch0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ShortInverseBatch1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ShortInverseBatch2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ShortInverseBatch3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ShortInverseBatch4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ShortInverseBatch5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ShortInverseBatch6
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ShortInverseBatch7
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SourceDictionary

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem short_inverse_batch (b a : Fin 8) (k : Fin 16) :
    monsterNortonUQInverseFastImage (monsterNortonShortQSource (Sum.inr (Sum.inr
      (monsterNortonLine01ShortInputCode (monsterNortonLine01ShortInverseBatchIndex b a),
        monsterNortonLine01ShortPhysicalColumn k)))) =
      qCentral (monsterNortonLine01ShortInversePhase
        (monsterNortonLine01ShortInverseBatchIndex b a) k) *
          monsterNortonLine01ShortInverseOutputQ
            (monsterNortonLine01ShortInverseBatchIndex b a) k := by
  fin_cases b
  · exact monsterNortonLine01ShortInverse_certificate_0 a k
  · exact monsterNortonLine01ShortInverse_certificate_1 a k
  · exact monsterNortonLine01ShortInverse_certificate_2 a k
  · exact monsterNortonLine01ShortInverse_certificate_3 a k
  · exact monsterNortonLine01ShortInverse_certificate_4 a k
  · exact monsterNortonLine01ShortInverse_certificate_5 a k
  · exact monsterNortonLine01ShortInverse_certificate_6 a k
  · exact monsterNortonLine01ShortInverse_certificate_7 a k

/-- All 1024 complete finite images agree with the proved actual inverse Norton Q action. -/
theorem monsterNortonLine01ShortInverse_certificate (a : Fin 64) (k : Fin 16) :
    monsterNortonUQInverseFastImage (monsterNortonShortQSource (Sum.inr (Sum.inr
      (monsterNortonLine01ShortInputCode a, monsterNortonLine01ShortPhysicalColumn k)))) =
      qCentral (monsterNortonLine01ShortInversePhase a k) *
        monsterNortonLine01ShortInverseOutputQ a k := by
  let b : Fin 8 := ⟨a.val / 8, by omega⟩
  let r : Fin 8 := ⟨a.val % 8, Nat.mod_lt _ (by norm_num)⟩
  have ha : a = monsterNortonLine01ShortInverseBatchIndex b r := by
    apply Fin.ext
    dsimp [b, r, monsterNortonLine01ShortInverseBatchIndex]
    omega
  rw [ha]
  exact short_inverse_batch b r k

/-- Each complete certificate determines the entire actual inverse Norton source X image. -/
theorem monsterNortonLine01ShortInverse_actual (a : Fin 64) (k : Fin 16) :
    (y555NortonActualU⁻¹).val (trialityXYZBasis 0 (finProdFinEquiv
      (monsterNortonLine01ShortInputCode a, monsterNortonLine01ShortPhysicalColumn k))) =
      griessConwayDecode (0, (qSign (monsterNortonLine01ShortInversePhase a k) •
        Pi.single (monsterNortonLine01ShortInverseOutput a k) 1, 0)) := by
  rw [monsterNortonSourceX_pure_short]
  apply monsterNortonU_inverse_short_basis_of_source_certificate
  rw [monsterNortonLine01ShortInverseOutputQ_actual]
  exact monsterNortonLine01ShortInverse_certificate a k

/-- A finite physical-column index, with irrelevant zero columns assigned index zero. -/
def monsterNortonLine01ShortPhysicalSlot : Fin 24 → Fin 16 :=
  ![0, 1, 0, 0, 2, 3, 4, 5, 6, 7, 8, 9,
    10, 11, 0, 0, 12, 0, 0, 13, 14, 0, 15, 0]

set_option maxRecDepth 10000 in
/-- On every nonzero numerator coordinate the finite slot recovers the actual physical column. -/
theorem monsterNortonLine01ShortPhysicalSlot_actual (i : Fin 24)
    (hi : monsterNortonUNumerator1 i 0 ≠ 0) :
    monsterNortonLine01ShortPhysicalColumn (monsterNortonLine01ShortPhysicalSlot i) = i := by
  revert i
  decide +kernel

/-- Every supported source X vector has the full actual signed inverse image in the table. -/
theorem monsterNortonLine01ShortInverse_supported (a : Fin 64) (i : Fin 24)
    (hi : monsterNortonUNumerator1 i 0 ≠ 0) :
    (y555NortonActualU⁻¹).val (trialityXYZBasis 0
      (finProdFinEquiv (monsterNortonLine01ShortInputCode a, i))) =
      griessConwayDecode (0,
        (qSign (monsterNortonLine01ShortInversePhase a (monsterNortonLine01ShortPhysicalSlot i)) •
          Pi.single (monsterNortonLine01ShortInverseOutput a
            (monsterNortonLine01ShortPhysicalSlot i)) 1, 0)) := by
  have h := monsterNortonLine01ShortInverse_actual a (monsterNortonLine01ShortPhysicalSlot i)
  rw [monsterNortonLine01ShortPhysicalSlot_actual i hi] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

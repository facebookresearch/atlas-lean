/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full actual U action on all 240 short units in the reached first-pair packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthQBatch0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthQBatch1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthQBatch2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthQBatch3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthQBatch4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthQBatch5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthQBatch6
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthQBatch7
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every reached image has its checked positive central coefficient. -/
theorem monsterNortonLine01PairEighthPhase_zero (e : Fin 240) :
    monsterNortonLine01PairEighthPhase e = 0 := by
  revert e
  decide +kernel

/-- All 240 actual Q images retain the entire verified central phase. -/
theorem monsterNortonLine01PairEighthQ_certificate (e : Fin 240) :
    monsterNortonUQFastImage
      (monsterNortonShortQ (monsterNortonLine01PairEighthShortInput e)) =
        monsterNortonShortQ (monsterNortonLine01PairEighthShortOutput e) := by
  have hc : qCentral (monsterNortonLine01PairEighthPhase e) = (1 : Q) := by
    rw [monsterNortonLine01PairEighthPhase_zero]
    rfl
  suffices h : monsterNortonUQFastImage
      (monsterNortonShortQ (monsterNortonLine01PairEighthShortInput e)) =
        qCentral (monsterNortonLine01PairEighthPhase e) *
          monsterNortonShortQ (monsterNortonLine01PairEighthShortOutput e) by
    simpa only [hc, one_mul] using h
  by_cases h0 : e.val < 30
  · have he : (⟨0 + (e.val - 0), by omega⟩ : Fin 240) = e :=
      Fin.ext (by change 0 + (e.val - 0) = e.val; omega)
    simpa only [he] using monsterNortonLine01PairEighthQ_batch0
      (⟨e.val - 0, by omega⟩ : Fin 30)
  by_cases h1 : e.val < 60
  · have he : (⟨30 + (e.val - 30), by omega⟩ : Fin 240) = e :=
      Fin.ext (by change 30 + (e.val - 30) = e.val; omega)
    simpa only [he] using monsterNortonLine01PairEighthQ_batch1
      (⟨e.val - 30, by omega⟩ : Fin 30)
  by_cases h2 : e.val < 90
  · have he : (⟨60 + (e.val - 60), by omega⟩ : Fin 240) = e :=
      Fin.ext (by change 60 + (e.val - 60) = e.val; omega)
    simpa only [he] using monsterNortonLine01PairEighthQ_batch2
      (⟨e.val - 60, by omega⟩ : Fin 30)
  by_cases h3 : e.val < 120
  · have he : (⟨90 + (e.val - 90), by omega⟩ : Fin 240) = e :=
      Fin.ext (by change 90 + (e.val - 90) = e.val; omega)
    simpa only [he] using monsterNortonLine01PairEighthQ_batch3
      (⟨e.val - 90, by omega⟩ : Fin 30)
  by_cases h4 : e.val < 150
  · have he : (⟨120 + (e.val - 120), by omega⟩ : Fin 240) = e :=
      Fin.ext (by change 120 + (e.val - 120) = e.val; omega)
    simpa only [he] using monsterNortonLine01PairEighthQ_batch4
      (⟨e.val - 120, by omega⟩ : Fin 30)
  by_cases h5 : e.val < 180
  · have he : (⟨150 + (e.val - 150), by omega⟩ : Fin 240) = e :=
      Fin.ext (by change 150 + (e.val - 150) = e.val; omega)
    simpa only [he] using monsterNortonLine01PairEighthQ_batch5
      (⟨e.val - 150, by omega⟩ : Fin 30)
  by_cases h6 : e.val < 210
  · have he : (⟨180 + (e.val - 180), by omega⟩ : Fin 240) = e :=
      Fin.ext (by change 180 + (e.val - 180) = e.val; omega)
    simpa only [he] using monsterNortonLine01PairEighthQ_batch6
      (⟨e.val - 180, by omega⟩ : Fin 30)
  have he : (⟨210 + (e.val - 210), by omega⟩ : Fin 240) = e :=
    Fin.ext (by change 210 + (e.val - 210) = e.val; omega)
  simpa only [he] using monsterNortonLine01PairEighthQ_batch7
    (⟨e.val - 210, by omega⟩ : Fin 30)

/-- Actual U sends every whole reached short unit to its full verified original image. -/
theorem monsterNortonLine01PairEighthU_unit (e : Fin 240) :
    y555NortonActualU.val
      (monsterNortonPureShort (monsterNortonLine01PairEighthShortInput e)) =
        monsterNortonPureShort (monsterNortonLine01PairEighthShortOutput e) := by
  rw [← monsterNortonULocal_generated]
  change localGriessRepresentation monsterNortonUFiber
    (griessConwayDecode (0, (Pi.single (monsterNortonLine01PairEighthShortInput e) 1, 0))) =
      griessConwayDecode (0, (Pi.single (monsterNortonLine01PairEighthShortOutput e) 1, 0))
  have hc : spinConjugation monsterNortonUFiber.val.1
      (monsterNortonShortQ (monsterNortonLine01PairEighthShortInput e)) =
        qCentral 0 * monsterNortonShortQ (monsterNortonLine01PairEighthShortOutput e) := by
    rw [monsterNortonUQImage_eq, monsterNortonUQFastImage_eq,
      show qCentral 0 = (1 : Q) from rfl, one_mul]
    exact monsterNortonLine01PairEighthQ_certificate e
  have hd := monsterNortonGriessShortBasis_of_Q_image monsterNortonUFiber
    (monsterNortonLine01PairEighthShortInput e) (monsterNortonLine01PairEighthShortOutput e) 0 hc
  simpa only [qSign_zero, one_smul] using hd

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

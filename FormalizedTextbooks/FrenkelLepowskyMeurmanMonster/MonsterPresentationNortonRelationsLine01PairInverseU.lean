/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete actual inverse-U action on the reached original octad packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairInverseQBatch0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairInverseQBatch1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairInverseQBatch2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairInverseQBatch3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairInverseQBatch4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairInverseQBatch5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairInverseQBatch6
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairInverseQBatch7
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All sixty-four full inverse-Q images are checked, with their actual central coefficient. -/
theorem monsterNortonLine01PairInverseQ_certificate (e : Fin 64) :
    monsterNortonUQInverseFastImage
      (monsterNortonShortQ (monsterNortonLine01PairInverseShortInput e)) =
        monsterNortonShortQ (monsterNortonLine01PairInverseShortOutput e) := by
  by_cases h0 : e.val < 8
  · have hlow : 0 ≤ e.val := by omega
    have he : (⟨0 + (e.val - 0), by omega⟩ : Fin 64) = e :=
      Fin.ext (by change 0 + (e.val - 0) = e.val; omega)
    simpa only [he] using monsterNortonLine01PairInverseQ_batch0
      (⟨e.val - 0, by omega⟩ : Fin 8)
  by_cases h1 : e.val < 16
  · have hlow : 8 ≤ e.val := by omega
    have he : (⟨8 + (e.val - 8), by omega⟩ : Fin 64) = e :=
      Fin.ext (by change 8 + (e.val - 8) = e.val; omega)
    simpa only [he] using monsterNortonLine01PairInverseQ_batch1
      (⟨e.val - 8, by omega⟩ : Fin 8)
  by_cases h2 : e.val < 24
  · have hlow : 16 ≤ e.val := by omega
    have he : (⟨16 + (e.val - 16), by omega⟩ : Fin 64) = e :=
      Fin.ext (by change 16 + (e.val - 16) = e.val; omega)
    simpa only [he] using monsterNortonLine01PairInverseQ_batch2
      (⟨e.val - 16, by omega⟩ : Fin 8)
  by_cases h3 : e.val < 32
  · have hlow : 24 ≤ e.val := by omega
    have he : (⟨24 + (e.val - 24), by omega⟩ : Fin 64) = e :=
      Fin.ext (by change 24 + (e.val - 24) = e.val; omega)
    simpa only [he] using monsterNortonLine01PairInverseQ_batch3
      (⟨e.val - 24, by omega⟩ : Fin 8)
  by_cases h4 : e.val < 40
  · have hlow : 32 ≤ e.val := by omega
    have he : (⟨32 + (e.val - 32), by omega⟩ : Fin 64) = e :=
      Fin.ext (by change 32 + (e.val - 32) = e.val; omega)
    simpa only [he] using monsterNortonLine01PairInverseQ_batch4
      (⟨e.val - 32, by omega⟩ : Fin 8)
  by_cases h5 : e.val < 48
  · have hlow : 40 ≤ e.val := by omega
    have he : (⟨40 + (e.val - 40), by omega⟩ : Fin 64) = e :=
      Fin.ext (by change 40 + (e.val - 40) = e.val; omega)
    simpa only [he] using monsterNortonLine01PairInverseQ_batch5
      (⟨e.val - 40, by omega⟩ : Fin 8)
  by_cases h6 : e.val < 56
  · have hlow : 48 ≤ e.val := by omega
    have he : (⟨48 + (e.val - 48), by omega⟩ : Fin 64) = e :=
      Fin.ext (by change 48 + (e.val - 48) = e.val; omega)
    simpa only [he] using monsterNortonLine01PairInverseQ_batch6
      (⟨e.val - 48, by omega⟩ : Fin 8)
  have he : (⟨56 + (e.val - 56), by omega⟩ : Fin 64) = e :=
    Fin.ext (by change 56 + (e.val - 56) = e.val; omega)
  simpa only [he] using monsterNortonLine01PairInverseQ_batch7
    (⟨e.val - 56, by omega⟩ : Fin 8)

/-- Actual inverse U maps each entire short unit to its checked original dictionary image. -/
theorem monsterNortonLine01PairInverseU_unit (e : Fin 64) :
    (y555NortonActualU⁻¹).val
      (monsterNortonPureShort (monsterNortonLine01PairInverseShortInput e)) =
        monsterNortonPureShort (monsterNortonLine01PairInverseShortOutput e) := by
  rw [← monsterNortonULocal_generated]
  change localGriessRepresentation (monsterNortonUFiber⁻¹)
    (griessConwayDecode (0, (Pi.single (monsterNortonLine01PairInverseShortInput e) 1, 0))) =
      griessConwayDecode (0, (Pi.single (monsterNortonLine01PairInverseShortOutput e) 1, 0))
  have hc : spinConjugation (monsterNortonUFiber⁻¹).val.1
      (monsterNortonShortQ (monsterNortonLine01PairInverseShortInput e)) =
        qCentral 0 * monsterNortonShortQ (monsterNortonLine01PairInverseShortOutput e) := by
    rw [monsterNortonUQInverseFastImage_eq, show qCentral 0 = (1 : Q) from rfl, one_mul]
    exact monsterNortonLine01PairInverseQ_certificate e
  have hd := monsterNortonGriessShortBasis_of_Q_image (monsterNortonUFiber⁻¹)
    (monsterNortonLine01PairInverseShortInput e) (monsterNortonLine01PairInverseShortOutput e) 0 hc
  simpa only [qSign_zero, one_smul] using hd

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

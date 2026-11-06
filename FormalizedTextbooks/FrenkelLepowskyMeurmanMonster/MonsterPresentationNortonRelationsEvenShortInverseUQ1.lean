/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Entire actual inverse-U transport of the second preferred short basis packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseUQ1Batch0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseUQ1Batch1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseUQ1Batch2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseUQ1Batch3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairInverseU

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All sixty-four actual inverse-U images retain the full preferred-lift central coefficients. -/
theorem monsterNortonEvenShortInverseUQ1_certificate (e : Fin 64) :
    monsterNortonUQInverseFastImage
      (monsterNortonShortQ (monsterNortonEvenShortInverseUInput 1 e)) =
      qCentral (monsterNortonEvenShortInverseUPhase 1 e) *
        monsterNortonShortQ (monsterNortonEvenShortInverseUOutput 1 e) := by
  by_cases h0 : e.val < 16
  · have he : (⟨0 + (e.val - 0), by omega⟩ : Fin 64) = e :=
      Fin.ext (by change 0 + (e.val - 0) = e.val; omega)
    simpa only [he] using monsterNortonEvenShortInverseUQ1_batch0
      (⟨e.val - 0, by omega⟩ : Fin 16)
  by_cases h1 : e.val < 32
  · have he : (⟨16 + (e.val - 16), by omega⟩ : Fin 64) = e :=
      Fin.ext (by change 16 + (e.val - 16) = e.val; omega)
    simpa only [he] using monsterNortonEvenShortInverseUQ1_batch1
      (⟨e.val - 16, by omega⟩ : Fin 16)
  by_cases h2 : e.val < 48
  · have he : (⟨32 + (e.val - 32), by omega⟩ : Fin 64) = e :=
      Fin.ext (by change 32 + (e.val - 32) = e.val; omega)
    simpa only [he] using monsterNortonEvenShortInverseUQ1_batch2
      (⟨e.val - 32, by omega⟩ : Fin 16)
  have he : (⟨48 + (e.val - 48), by omega⟩ : Fin 64) = e :=
    Fin.ext (by change 48 + (e.val - 48) = e.val; omega)
  simpa only [he] using monsterNortonEvenShortInverseUQ1_batch3
    (⟨e.val - 48, by omega⟩ : Fin 16)

private noncomputable def shortLift : (GriessShortIndex → ℝ) →ₗ[ℝ] GriessSpace :=
  griessConwayDecodeLinear.comp
    ((LinearMap.inr ℝ _ _).comp (LinearMap.inl ℝ _ _))

/-- Each actual inverse-U operator image is the whole signed preferred original short unit. -/
theorem monsterNortonEvenShortInverseUQ1_unit (e : Fin 64) :
    (y555NortonActualU⁻¹).val (monsterNortonPureShort (monsterNortonEvenShortInverseUInput 1 e)) =
      qSign (monsterNortonEvenShortInverseUPhase 1 e) •
        monsterNortonPureShort (monsterNortonEvenShortInverseUOutput 1 e) := by
  rw [← monsterNortonULocal_generated]
  change localGriessRepresentation (monsterNortonUFiber⁻¹)
    (griessConwayDecode (0, (Pi.single (monsterNortonEvenShortInverseUInput 1 e) 1, 0))) = _
  have hc : spinConjugation (monsterNortonUFiber⁻¹).val.1
      (monsterNortonShortQ (monsterNortonEvenShortInverseUInput 1 e)) =
      qCentral (monsterNortonEvenShortInverseUPhase 1 e) *
        monsterNortonShortQ (monsterNortonEvenShortInverseUOutput 1 e) := by
    rw [monsterNortonUQInverseFastImage_eq]
    exact monsterNortonEvenShortInverseUQ1_certificate e
  have hd := monsterNortonGriessShortBasis_of_Q_image (monsterNortonUFiber⁻¹)
    (monsterNortonEvenShortInverseUInput 1 e) (monsterNortonEvenShortInverseUOutput 1 e)
    (monsterNortonEvenShortInverseUPhase 1 e) hc
  have hs : griessConwayDecode
      (0, (qSign (monsterNortonEvenShortInverseUPhase 1 e) •
        Pi.single (monsterNortonEvenShortInverseUOutput 1 e) 1, 0)) =
      qSign (monsterNortonEvenShortInverseUPhase 1 e) •
        monsterNortonPureShort (monsterNortonEvenShortInverseUOutput 1 e) :=
    shortLift.map_smul (qSign (monsterNortonEvenShortInverseUPhase 1 e))
      (Pi.single (monsterNortonEvenShortInverseUOutput 1 e) 1)
  exact hd.trans hs

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

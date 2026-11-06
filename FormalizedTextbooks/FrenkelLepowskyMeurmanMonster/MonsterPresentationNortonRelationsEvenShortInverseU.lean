/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete preferred-Q and short-unit inverse-U transport for every reached Fourier packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseUPhysicalData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseUPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUInversePhysicalCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortVectorQTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairInverseU

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Every exact integer image is the entire actual physical inverse-U vector image. -/
theorem monsterNortonEvenShortInverseU_vector (k : Fin 23) (e : Fin 64) :
    (monsterNortonUFiber.val.2⁻¹).val
      (griessShortVector (monsterNortonEvenShortInverseUInput k e)) =
        (monsterNortonEvenShortInverseUPhysicalSign k e : ℝ) •
          griessShortVector (monsterNortonEvenShortInverseUOutput k e) := by
  apply monsterNortonUInversePhysical_of_certificate
  intro i
  rw [monsterNortonEvenShortInverseUInputIntegral_actual,
    monsterNortonEvenShortInverseUIntegral_actual]
  exact monsterNortonEvenShortInverseUPhysical_certificate k e i

/-- Each preferred output is the true whole physical inverse image, up to global vector sign. -/
theorem monsterNortonEvenShortInverseU_vector_sign (k : Fin 23) (e : Fin 64) :
    (monsterNortonUFiber.val.2⁻¹).val
      (griessShortVector (monsterNortonEvenShortInverseUInput k e)) =
      griessShortVector (monsterNortonEvenShortInverseUOutput k e) ∨
    (monsterNortonUFiber.val.2⁻¹).val
      (griessShortVector (monsterNortonEvenShortInverseUInput k e)) =
      -griessShortVector (monsterNortonEvenShortInverseUOutput k e) := by
  have h := monsterNortonEvenShortInverseU_vector k e
  rcases monsterNortonEvenShortInverseUPhysicalSign_cases k e with hp | hn
  · rw [hp, Int.cast_one, one_smul] at h
    exact Or.inl h
  · rw [hn, Int.cast_neg, Int.cast_one, neg_one_smul] at h
    exact Or.inr h

/-- All complete actual inverse-U preferred-Q images retain every central coefficient. -/
theorem monsterNortonEvenShortInverseU_Q_image (k : Fin 23) (e : Fin 64) :
    spinConjugation (monsterNortonUFiber⁻¹).val.1
      (monsterNortonShortQ (monsterNortonEvenShortInverseUInput k e)) =
        qCentral (monsterNortonEvenShortInverseUPhase k e) *
          monsterNortonShortQ (monsterNortonEvenShortInverseUOutput k e) :=
  monsterNortonShortQ_image_of_vector_phase (monsterNortonUFiber⁻¹) _ _ _
    (monsterNortonEvenShortInverseU_vector_sign k e)
    (monsterNortonEvenShortInverseUPhase_actual k e)

private noncomputable def shortLift : (GriessShortIndex → ℝ) →ₗ[ℝ] GriessSpace :=
  griessConwayDecodeLinear.comp
    ((LinearMap.inr ℝ _ _).comp (LinearMap.inl ℝ _ _))

/-- Every whole actual short unit has its checked inverse-U label and full preferred-lift sign. -/
theorem monsterNortonEvenShortInverseU_unit (k : Fin 23) (e : Fin 64) :
    (y555NortonActualU⁻¹).val (monsterNortonPureShort (monsterNortonEvenShortInverseUInput k e)) =
      qSign (monsterNortonEvenShortInverseUPhase k e) •
        monsterNortonPureShort (monsterNortonEvenShortInverseUOutput k e) := by
  rw [← monsterNortonULocal_generated]
  change localGriessRepresentation (monsterNortonUFiber⁻¹)
    (griessConwayDecode (0, (Pi.single (monsterNortonEvenShortInverseUInput k e) 1, 0))) = _
  have h := monsterNortonGriessShortBasis_of_Q_image (monsterNortonUFiber⁻¹)
    (monsterNortonEvenShortInverseUInput k e) (monsterNortonEvenShortInverseUOutput k e)
    (monsterNortonEvenShortInverseUPhase k e) (monsterNortonEvenShortInverseU_Q_image k e)
  have hs : griessConwayDecode (0, (qSign (monsterNortonEvenShortInverseUPhase k e) •
      Pi.single (monsterNortonEvenShortInverseUOutput k e) 1, 0)) =
      qSign (monsterNortonEvenShortInverseUPhase k e) •
        monsterNortonPureShort (monsterNortonEvenShortInverseUOutput k e) :=
    shortLift.map_smul (qSign (monsterNortonEvenShortInverseUPhase k e))
      (Pi.single (monsterNortonEvenShortInverseUOutput k e) 1)
  exact h.trans hs

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Whole actual source U images of all eleven opposite signed-pair basis inputs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortUpperPairsData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUPhysicalTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQSelectedPhaseForward
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortVectorQTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Full positive preferred lifts encoded by the actual opposite-family input masks. -/
def monsterNortonEvenShortUpperInputQ (k : Fin 11) : Q :=
  ⟨ofAdd (fun i : Fin 24 => if (monsterNortonEvenShortUpperUMask k).testBit i.val
    then 1 else 0), 1⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Verify all original hyperbolic input coordinates and the complete coefficient-zero lift.
/-- Every stored mask is the actual original preferred-Q opposite-family input. -/
theorem monsterNortonEvenShortUpperInputQ_actual (k : Fin 11) :
    monsterNortonShortQ (monsterNortonEvenShortUpperInput k) =
      monsterNortonEvenShortUpperInputQ k := by
  unfold monsterNortonShortQ monsterNortonEvenShortUpperInputQ
  rw [monsterNortonEvenShortUpperInputIntegral_actual]
  apply NormalizedCocycleExtension.Extension.ext
  · funext i
    revert k i
    decide +kernel
  · rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Verify all 264 physical integer output coordinates through the genuine source U matrix.
/-- Each actual physical U image has precisely the displayed global representative sign. -/
theorem monsterNortonEvenShortUpperUPhysical_certificate (k : Fin 11) (i : Fin 24) :
    (monsterNortonUNumerator1 *ᵥ monsterNortonEvenShortUpperInputIntegral k) i =
      4 * monsterNortonEvenShortUpperUPhysicalSign k *
        monsterNortonEvenShortUpperUIntegral k i := by
  revert k i
  decide +kernel

/-- The finite physical transport certificate determines the whole actual real vector image. -/
theorem monsterNortonEvenShortUpperUPhysical_actual (k : Fin 11) :
    monsterNortonUFiber.val.2.val (griessShortVector (monsterNortonEvenShortUpperInput k)) =
      (monsterNortonEvenShortUpperUPhysicalSign k : ℝ) •
        griessShortVector (monsterNortonEvenShortUpperUOutput k) := by
  apply monsterNortonUPhysical_of_certificate
  intro i
  rw [monsterNortonEvenShortUpperInputIntegral_actual,
    monsterNortonEvenShortUpperUIntegral_actual]
  exact monsterNortonEvenShortUpperUPhysical_certificate k i

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Verify all eleven complete central coefficients through the actual full Q generator cache.
/-- Every true opposite-family U output has its genuine positive preferred-Q phase. -/
theorem monsterNortonEvenShortUpperUPhase_actual (k : Fin 11) :
    toAdd (spinConjugation monsterNortonUFiber.val.1
      (monsterNortonShortQ (monsterNortonEvenShortUpperInput k))).coeff = 0 := by
  rw [monsterNortonUQImage_eq, monsterNortonUQFastImage_eq,
    monsterNortonEvenShortUpperInputQ_actual, monsterNortonUQFastImage_selected_phase]
  revert k
  decide +kernel

/-- Every stored physical representative sign is precisely plus or minus one. -/
theorem monsterNortonEvenShortUpperUPhysicalSign_unit (k : Fin 11) :
    monsterNortonEvenShortUpperUPhysicalSign k = 1 ∨
      monsterNortonEvenShortUpperUPhysicalSign k = -1 := by
  revert k
  decide +kernel

/-- Physical transport and the actual positive central phase identify the full preferred Q image. -/
theorem monsterNortonEvenShortUpperU_Q_image (k : Fin 11) :
    spinConjugation monsterNortonUFiber.val.1
      (monsterNortonShortQ (monsterNortonEvenShortUpperInput k)) =
        monsterNortonShortQ (monsterNortonEvenShortUpperUOutput k) := by
  have hv := monsterNortonEvenShortUpperUPhysical_actual k
  have hh : monsterNortonUFiber.val.2.val
      (griessShortVector (monsterNortonEvenShortUpperInput k)) =
      griessShortVector (monsterNortonEvenShortUpperUOutput k) ∨
      monsterNortonUFiber.val.2.val (griessShortVector (monsterNortonEvenShortUpperInput k)) =
        -griessShortVector (monsterNortonEvenShortUpperUOutput k) := by
    rcases monsterNortonEvenShortUpperUPhysicalSign_unit k with hp | hn
    · left
      simpa only [hp, Int.cast_one, one_smul] using hv
    · right
      simpa only [hn, Int.cast_neg, Int.cast_one, neg_one_smul] using hv
  have h := monsterNortonShortQ_image_of_vector_phase monsterNortonUFiber
    (monsterNortonEvenShortUpperInput k) (monsterNortonEvenShortUpperUOutput k) 0 hh
    (monsterNortonEvenShortUpperUPhase_actual k)
  simpa only [show qCentral 0 = (1 : Q) from rfl, one_mul] using h

/-- Literal actual U takes each entire opposite-family pair unit to its genuine source output. -/
theorem monsterNortonEvenShortUpperU_actual (k : Fin 11) :
    y555NortonActualU.val (monsterNortonPureShort (monsterNortonEvenShortUpperInput k)) =
      monsterNortonPureShort (monsterNortonEvenShortUpperUOutput k) := by
  rw [← monsterNortonULocal_generated]
  change localGriessRepresentation monsterNortonUFiber
    (griessConwayDecode (0, (Pi.single (monsterNortonEvenShortUpperInput k) 1, 0))) =
      griessConwayDecode (0, (Pi.single (monsterNortonEvenShortUpperUOutput k) 1, 0))
  have h := monsterNortonGriessShortBasis_of_Q_image monsterNortonUFiber
    (monsterNortonEvenShortUpperInput k) (monsterNortonEvenShortUpperUOutput k) 0
    (by rw [show qCentral 0 = (1 : Q) from rfl, one_mul]
        exact monsterNortonEvenShortUpperU_Q_image k)
  simpa only [qSign_zero, one_smul] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

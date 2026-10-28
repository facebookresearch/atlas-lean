/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete phase-correct actual U transport of the eight additional octad-three units. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadThreeUSupplementData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Check the 192 parity coordinates in the original integral Leech basis.
/-- Every cached input lattice parity coordinate agrees with its complete actual dictionary. -/
theorem monsterNortonOctadThreeSupplementInputParity_actual (i : Fin 8) (j : Fin 24) :
    integerParity
      (monsterNortonLeechCoordinates (monsterNortonOctadThreeSupplementInputIntegral i)) j =
      if (monsterNortonOctadThreeSupplementInputParity i).testBit j.val then 1 else 0 := by
  revert i j
  decide +kernel

/-- Full coefficient-zero lift encoded by each stored genuine input hyperbolic mask. -/
def monsterNortonOctadThreeSupplementInputQ (i : Fin 8) : Q :=
  ⟨ofAdd (fun j : Fin 24 =>
    if (monsterNortonOctadThreeSupplementInputMask i).testBit j.val then 1 else 0), 1⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Check every hyperbolic coordinate after the actual integral Leech parity has been transported.
/-- Every pool mask is its complete actual original preferred input, including the zero phase. -/
theorem monsterNortonOctadThreeSupplementInputQ_actual (i : Fin 8) :
    monsterNortonShortQ (monsterNortonOctadThreeSupplementInput i) =
      monsterNortonOctadThreeSupplementInputQ i := by
  unfold monsterNortonShortQ monsterNortonOctadThreeSupplementInputQ
  rw [monsterNortonOctadThreeSupplementInputIntegral_actual]
  have hpar : integerParity (monsterNortonLeechCoordinates
      (monsterNortonOctadThreeSupplementInputIntegral i)) =
        fun j : Fin 24 =>
          if (monsterNortonOctadThreeSupplementInputParity i).testBit j.val then 1 else 0 :=
    funext (monsterNortonOctadThreeSupplementInputParity_actual i)
  rw [hpar]
  clear hpar
  apply NormalizedCocycleExtension.Extension.ext
  · funext j
    revert i j
    decide +kernel
  · rfl

set_option maxHeartbeats 8000000 in
-- Check the actual central coefficient of every complete preferred input.
/-- Actual U gives the positive preferred output phase on all eight additional inputs. -/
theorem monsterNortonOctadThreeSupplementPhase_actual (i : Fin 8) :
    toAdd (spinConjugation monsterNortonUFiber.val.1
      (monsterNortonShortQ (monsterNortonOctadThreeSupplementInput i))).coeff = 0 := by
  rw [monsterNortonOctadThreeSupplementInputQ_actual, monsterNortonUQImage_eq,
    monsterNortonUQFastImage_eq, monsterNortonUQFastImage_selected_phase]
  revert i
  decide +kernel

/-- The finite physical certificate gives the complete real-vector transport in actual Co0. -/
theorem monsterNortonOctadThreeSupplementPhysical_actual (i : Fin 8) :
    monsterNortonUFiber.val.2.val (griessShortVector (monsterNortonOctadThreeSupplementInput i)) =
      (monsterNortonOctadThreeSupplementPhysicalSign i : ℝ) •
        griessShortVector (monsterNortonOctadThreeSupplementOutput i) := by
  apply monsterNortonUPhysical_of_certificate
  intro j
  rw [monsterNortonOctadThreeSupplementInputIntegral_actual,
    monsterNortonOctadThreeSupplementOutputIntegral_actual]
  exact monsterNortonOctadThreeSupplementPhysical_certificate i j

/-- Every stored physical representative scalar is exactly plus or minus one. -/
theorem monsterNortonOctadThreeSupplementPhysicalSign_unit (i : Fin 8) :
    monsterNortonOctadThreeSupplementPhysicalSign i = 1 ∨
      monsterNortonOctadThreeSupplementPhysicalSign i = -1 := by
  revert i
  decide +kernel

/-- Physical transport and the actual positive central phase identify the full preferred Q image. -/
theorem monsterNortonOctadThreeSupplement_Q_image (k : Fin 8) :
    spinConjugation monsterNortonUFiber.val.1
      (monsterNortonShortQ (monsterNortonOctadThreeSupplementInput k)) =
        monsterNortonShortQ (monsterNortonOctadThreeSupplementOutput k) := by
  have hv := monsterNortonOctadThreeSupplementPhysical_actual k
  have hh : monsterNortonUFiber.val.2.val
      (griessShortVector (monsterNortonOctadThreeSupplementInput k)) =
      griessShortVector (monsterNortonOctadThreeSupplementOutput k) ∨
      monsterNortonUFiber.val.2.val (griessShortVector (monsterNortonOctadThreeSupplementInput k)) =
        -griessShortVector (monsterNortonOctadThreeSupplementOutput k) := by
    rcases monsterNortonOctadThreeSupplementPhysicalSign_unit k with hp | hn
    · left
      simpa only [hp, Int.cast_one, one_smul] using hv
    · right
      simpa only [hn, Int.cast_neg, Int.cast_one, neg_one_smul] using hv
  have h := monsterNortonShortQ_image_of_vector_phase monsterNortonUFiber
    (monsterNortonOctadThreeSupplementInput k) (monsterNortonOctadThreeSupplementOutput k) 0 hh
    (monsterNortonOctadThreeSupplementPhase_actual k)
  simpa only [show qCentral 0 = (1 : Q) from rfl, one_mul] using h

/-- Literal actual U takes each entire additional octad-three unit to its genuine source output. -/
theorem monsterNortonOctadThreeSupplement_actual (k : Fin 8) :
    y555NortonActualU.val (monsterNortonPureShort (monsterNortonOctadThreeSupplementInput k)) =
      monsterNortonPureShort (monsterNortonOctadThreeSupplementOutput k) := by
  rw [← monsterNortonULocal_generated]
  change localGriessRepresentation monsterNortonUFiber
    (griessConwayDecode (0, (Pi.single (monsterNortonOctadThreeSupplementInput k) 1, 0))) =
      griessConwayDecode (0, (Pi.single (monsterNortonOctadThreeSupplementOutput k) 1, 0))
  have h := monsterNortonGriessShortBasis_of_Q_image monsterNortonUFiber
    (monsterNortonOctadThreeSupplementInput k) (monsterNortonOctadThreeSupplementOutput k) 0
    (by rw [show qCentral 0 = (1 : Q) from rfl, one_mul]
        exact monsterNortonOctadThreeSupplement_Q_image k)
  simpa only [qSign_zero, one_smul] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

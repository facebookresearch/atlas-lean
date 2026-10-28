/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual Norton images of the preferred twenty-four short basis vectors. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQOctadCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadOrdering

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The image lies in the actual signed-octad family precisely at these entries. -/
def monsterNortonShortBasisUIsOctad : Fin 24 → Bool :=
  ![true, true, true, true, true, true, true, true,
    true, true, true, false, true, true, false, false,
    true, true, true, true, true, true, false, false]

/-- Source code labels of the reached actual short classes. -/
def monsterNortonShortBasisUCode : Fin 24 → Fin 4096 :=
  ![1106, 339, 349, 3420, 1256, 489, 487, 1204, 437, 443,
    3342, 1280, 1204, 3342, 1536, 1792, 1490, 1378, 1426, 1394, 1298, 1346, 82, 1107]

/-- The odd-family code labels at the four odd images, with unused entries zero. -/
def monsterNortonShortBasisUOddCode : Fin 24 → Fin 2048 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1280, 0, 0, 1536, 1792, 0, 0, 0, 0, 0, 0, 82, 1107]

/-- Local sign labels at octad images and physical positions at odd images. -/
def monsterNortonShortBasisUPosition : Fin 24 → Fin 64 :=
  ![39, 19, 7, 57, 56, 19, 7, 7, 19, 7, 30, 2, 57, 33, 13, 13, 27, 29, 27, 29, 45, 57, 13, 13]

/-- The physical singleton position at each odd image, with unused entries zero. -/
def monsterNortonShortBasisUOddPosition : Fin 24 → Fin 24 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 13, 13, 0, 0, 0, 0, 0, 0, 13, 13]

/-- Eight ordered physical positions of every reached octad, avoiding dictionary enumeration. -/
def monsterNortonShortBasisUOctadPositions : Fin 24 → Fin 8 → Fin 24 :=
  ![![1, 2, 3, 5, 9, 12, 19, 22],
    ![2, 3, 6, 7, 8, 9, 12, 13],
    ![2, 3, 4, 5, 10, 11, 12, 13],
    ![0, 2, 3, 5, 9, 13, 16, 20],
    ![1, 2, 3, 7, 10, 13, 19, 20],
    ![2, 3, 5, 6, 8, 10, 20, 22],
    ![2, 3, 4, 7, 9, 11, 20, 22],
    ![1, 2, 3, 6, 11, 13, 16, 22],
    ![2, 3, 5, 7, 8, 11, 16, 19],
    ![2, 3, 4, 6, 9, 10, 16, 19],
    ![0, 2, 3, 4, 8, 13, 19, 22],
    ![0, 1, 2, 3, 4, 5, 6, 7],
    ![1, 2, 3, 6, 11, 13, 16, 22],
    ![0, 2, 3, 4, 8, 13, 19, 22],
    ![0, 1, 2, 3, 4, 5, 6, 7],
    ![0, 1, 2, 3, 4, 5, 6, 7],
    ![1, 7, 9, 12, 13, 14, 19, 21],
    ![1, 5, 10, 12, 13, 15, 19, 23],
    ![1, 6, 9, 12, 13, 15, 17, 22],
    ![1, 5, 11, 12, 13, 14, 18, 22],
    ![1, 5, 6, 7, 9, 12, 18, 23],
    ![1, 5, 9, 10, 11, 12, 17, 21],
    ![0, 1, 2, 3, 4, 5, 6, 7],
    ![0, 1, 2, 3, 4, 5, 6, 7]]

/-- Every code used as an octad really has weight eight. -/
theorem monsterNortonShortBasisU_octad_weight (j : Fin 24)
    (hj : monsterNortonShortBasisUIsOctad j = true) :
    golayMaskWeight (golayEncodedMask (monsterNortonShortBasisUCode j).val) = 8 := by
  revert hj
  fin_cases j <;> decide +kernel

/-- Every displayed physical octad position lies in its actual source octad. -/
theorem monsterNortonShortBasisU_octad_mem (j : Fin 24)
    (hj : monsterNortonShortBasisUIsOctad j = true) (k : Fin 8) :
    (golayEncodedMask (monsterNortonShortBasisUCode j).val).testBit
      (monsterNortonShortBasisUOctadPositions j k).val = true := by
  revert hj k
  fin_cases j <;> decide +kernel

/-- Every eight-position table is strictly increasing in the actual physical order. -/
theorem monsterNortonShortBasisU_octad_strictMono (j : Fin 24)
    (hj : monsterNortonShortBasisUIsOctad j = true) :
    StrictMono (monsterNortonShortBasisUOctadPositions j) := by
  revert hj
  fin_cases j <;> decide +kernel

/-- The actual preferred short labels reached by the complete Norton word. -/
noncomputable def monsterNortonShortBasisUOutput (j : Fin 24) : GriessShortIndex :=
  if hj : monsterNortonShortBasisUIsOctad j = true then
    Sum.inr (Sum.inl (monsterNortonOctadIndex (monsterNortonShortBasisUCode j)
      (monsterNortonShortBasisU_octad_weight j hj), monsterNortonShortBasisUPosition j))
  else Sum.inr (Sum.inr
    (monsterNortonShortBasisUOddCode j, monsterNortonShortBasisUOddPosition j))

/-- The finite source-coordinate lift of the same output, including its preferred phase. -/
def monsterNortonShortBasisUQOutput (j : Fin 24) : Q :=
  if monsterNortonShortBasisUIsOctad j = true then
    monsterNortonOctadQSource (monsterNortonShortBasisUCode j)
      (monsterNortonShortBasisUOctadPositions j) (monsterNortonShortBasisUPosition j)
  else monsterNortonShortQSource (Sum.inr (Sum.inr
    (monsterNortonShortBasisUOddCode j, monsterNortonShortBasisUOddPosition j)))

/-- All enumeration transports are proved before any finite arithmetic certificate is checked. -/
theorem monsterNortonShortBasisUQOutput_actual (j : Fin 24) :
    monsterNortonShortQSource (monsterNortonShortBasisUOutput j) =
      monsterNortonShortBasisUQOutput j := by
  unfold monsterNortonShortBasisUOutput monsterNortonShortBasisUQOutput
  by_cases hj : monsterNortonShortBasisUIsOctad j = true
  · simp only [hj, dite_true, ite_true]
    apply monsterNortonOctadQSource_actual
    exact monsterNortonOctadIndex_coordinate_of_strictMono _ _ _
      (monsterNortonShortBasisU_octad_mem j hj) (monsterNortonShortBasisU_octad_strictMono j hj)
  · simp [hj]

/-- The complete central signs of these actual preferred-short images. -/
def monsterNortonShortBasisUPhase : Fin 24 → ZMod 2 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 40000000 in
-- Ordinary kernel checking retains both binary coordinates and the central coefficient.
/-- All twenty-four signed short images follow from the actual complete Q-action cache. -/
theorem monsterNortonShortBasisU_certificate (j : Fin 24) :
    monsterNortonUQFastImage (monsterNortonShortQSource (monsterNortonShortBasisIndex j)) =
      qCentral (monsterNortonShortBasisUPhase j) * monsterNortonShortBasisUQOutput j := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change (fun i : Fin 24 => toAdd (monsterNortonUQFastImage
      (monsterNortonShortQSource (monsterNortonShortBasisIndex j))).base i) =
        (fun i : Fin 24 => toAdd (qCentral (monsterNortonShortBasisUPhase j) *
          monsterNortonShortBasisUQOutput j).base i)
    fin_cases j <;> decide +kernel
  · apply toAdd.injective
    fin_cases j <;> decide +kernel

/-- Each finite certificate determines the entire actual Griess short-basis image. -/
theorem monsterNortonShortBasisU_actual (j : Fin 24) :
    y555NortonActualU.val
      (griessConwayDecode (0, (Pi.single (monsterNortonShortBasisIndex j) 1, 0))) =
      griessConwayDecode (0, (qSign (monsterNortonShortBasisUPhase j) •
        Pi.single (monsterNortonShortBasisUOutput j) 1, 0)) := by
  apply monsterNortonU_short_basis_of_source_certificate
  rw [monsterNortonShortBasisUQOutput_actual]
  exact monsterNortonShortBasisU_certificate j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

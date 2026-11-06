/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual opposite pair and U octad labels for the second preferred basis input. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQImageCache

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix

/-- The opposite signed-pair family at physical coordinates zero and two. -/
noncomputable def monsterNortonEvenShortSecondUpperShortInput : GriessShortIndex :=
  Sum.inl (1, griessPairIndex 0 2 (by decide))

/-- Its actual physical integer vector. -/
def monsterNortonEvenShortSecondUpperShortIntegral : Fin 24 → ℤ :=
  fun i => 4 * (if i = 0 then 1 else 0) + 4 * (if i = 2 then 1 else 0)

/-- The finite pair formula agrees with the original Conway shortest-vector dictionary. -/
theorem monsterNortonEvenShortSecondUpperShortIntegral_actual :
    griessShortIntegral monsterNortonEvenShortSecondUpperShortInput =
      monsterNortonEvenShortSecondUpperShortIntegral := by
  simp only [monsterNortonEvenShortSecondUpperShortInput, griessShortIntegral,
    griessPairIndex_coordinates, show (0 : Fin 24) < 2 by decide, ite_true,
    show (1 : Fin 2) ≠ 0 by decide, ite_false]
  funext i
  simp only [monsterNortonEvenShortSecondUpperShortIntegral]

/-- The eight actual physical positions of the octad reached under Norton U. -/
def monsterNortonEvenShortSecondUpperUOctadPositions : Fin 8 → Fin 24 :=
  ![0, 5, 6, 7, 8, 12, 16, 20]

/-- This source code is an actual weight-eight Golay codeword. -/
theorem monsterNortonEvenShortSecondUpperUOctad_weight :
    golayMaskWeight (golayEncodedMask 3087) = 8 := by
  decide +kernel

private theorem position_mem (k : Fin 8) :
    (golayEncodedMask 3087).testBit (monsterNortonEvenShortSecondUpperUOctadPositions k).val =
      true := by
  revert k
  decide +kernel

private theorem positions_mem (i : Fin 24) :
    i ∈ golayMaskSupport (golayEncodedMask 3087) ↔
      i ∈ List.ofFn monsterNortonEvenShortSecondUpperUOctadPositions := by
  revert i
  decide +kernel

private theorem positions_sorted :
    List.SortedLT (List.ofFn monsterNortonEvenShortSecondUpperUOctadPositions) := by
  decide +kernel

private theorem positions_sort :
    (golayMaskSupport (golayEncodedMask 3087)).sort =
      List.ofFn monsterNortonEvenShortSecondUpperUOctadPositions := by
  apply (golayMaskSupport _).sortedLT_sort.eq_of_mem_iff positions_sorted
  intro i
  simp only [Finset.mem_sort]
  exact positions_mem i

private theorem position_index (k : Fin 8) :
    (golayMaskSupport (golayEncodedMask 3087)).sort.idxOf
      (monsterNortonEvenShortSecondUpperUOctadPositions k) = k.val := by
  rw [positions_sort]
  revert k
  decide +kernel

/-- The displayed positions are precisely the original dictionary's increasing octad order. -/
theorem monsterNortonEvenShortSecondUpperUOctad_coordinate (k : Fin 8) :
    golayOctadCoordinate
      (monsterNortonOctadIndex 3087 monsterNortonEvenShortSecondUpperUOctad_weight) k =
        monsterNortonEvenShortSecondUpperUOctadPositions k :=
  monsterNortonOctadIndex_coordinate (3087 : Fin 4096)
    monsterNortonEvenShortSecondUpperUOctad_weight
    monsterNortonEvenShortSecondUpperUOctadPositions position_mem position_index k

/-- The actual octad-short label, with its original even-sign label45. -/
noncomputable def monsterNortonEvenShortSecondUpperUShortOutput : GriessShortIndex :=
  Sum.inr (Sum.inl
    (monsterNortonOctadIndex 3087 monsterNortonEvenShortSecondUpperUOctad_weight, 45))

/-- The entire physical integer vector of this octad-short output. -/
def monsterNortonEvenShortSecondUpperUShortIntegral : Fin 24 → ℤ :=
  monsterNortonOctadIntegral 3087 monsterNortonEvenShortSecondUpperUOctadPositions 45

/-- The output vector is the actual signed shortest-vector dictionary value. -/
theorem monsterNortonEvenShortSecondUpperUShortIntegral_actual :
    griessShortIntegral monsterNortonEvenShortSecondUpperUShortOutput =
      monsterNortonEvenShortSecondUpperUShortIntegral :=
  monsterNortonOctadIntegral_eq (3087 : Fin 4096) monsterNortonEvenShortSecondUpperUOctad_weight
    monsterNortonEvenShortSecondUpperUOctadPositions
    monsterNortonEvenShortSecondUpperUOctad_coordinate 45

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

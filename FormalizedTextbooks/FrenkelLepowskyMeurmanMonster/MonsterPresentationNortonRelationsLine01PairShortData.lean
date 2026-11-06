/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual pair and octad labels for the first finite plus-space line-square test. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQImageCache

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix

/-- The genuine first signed pair-short coordinate. -/
noncomputable def monsterNortonLine01PairShortInput : GriessShortIndex :=
  Sum.inl (0, griessPairIndex 0 1 (by decide))

/-- Its actual physical integer vector. -/
def monsterNortonLine01PairShortIntegral : Fin 24 → ℤ :=
  fun i => 4 * (if i = 0 then 1 else 0) - 4 * (if i = 1 then 1 else 0)

/-- The finite pair formula agrees with the original Conway shortest-vector dictionary. -/
theorem monsterNortonLine01PairShortIntegral_actual :
    griessShortIntegral monsterNortonLine01PairShortInput =
      monsterNortonLine01PairShortIntegral := by
  simp only [monsterNortonLine01PairShortInput, griessShortIntegral,
    griessPairIndex_coordinates, show (0 : Fin 24) < 1 by decide, ite_true]
  funext i
  simp only [monsterNortonLine01PairShortIntegral]
  ring

/-- The eight actual physical positions of the octad reached under Norton U. -/
def monsterNortonLine01PairUOctadPositions : Fin 8 → Fin 24 := ![1, 5, 6, 7, 8, 13, 19, 22]

/-- This source code is an actual weight-eight Golay codeword. -/
theorem monsterNortonLine01PairUOctad_weight : golayMaskWeight (golayEncodedMask 1281) = 8 := by
  decide +kernel

private theorem position_mem (k : Fin 8) :
    (golayEncodedMask 1281).testBit (monsterNortonLine01PairUOctadPositions k).val = true := by
  revert k
  decide +kernel

private theorem positions_mem (i : Fin 24) :
    i ∈ golayMaskSupport (golayEncodedMask 1281) ↔
      i ∈ List.ofFn monsterNortonLine01PairUOctadPositions := by
  revert i
  decide +kernel

private theorem positions_sorted :
    List.SortedLT (List.ofFn monsterNortonLine01PairUOctadPositions) := by
  decide +kernel

private theorem positions_sort :
    (golayMaskSupport (golayEncodedMask 1281)).sort =
      List.ofFn monsterNortonLine01PairUOctadPositions := by
  apply (golayMaskSupport _).sortedLT_sort.eq_of_mem_iff positions_sorted
  intro i
  simp only [Finset.mem_sort]
  exact positions_mem i

private theorem position_index (k : Fin 8) :
    (golayMaskSupport (golayEncodedMask 1281)).sort.idxOf
      (monsterNortonLine01PairUOctadPositions k) = k.val := by
  rw [positions_sort]
  revert k
  decide +kernel

/-- The displayed positions are precisely the original dictionary's increasing octad order. -/
theorem monsterNortonLine01PairUOctad_coordinate (k : Fin 8) :
    golayOctadCoordinate
      (monsterNortonOctadIndex 1281 monsterNortonLine01PairUOctad_weight) k =
        monsterNortonLine01PairUOctadPositions k :=
  monsterNortonOctadIndex_coordinate (1281 : Fin 4096) monsterNortonLine01PairUOctad_weight
    monsterNortonLine01PairUOctadPositions position_mem position_index k

/-- The actual octad-short label, with its original even-sign label45. -/
noncomputable def monsterNortonLine01PairUShortOutput : GriessShortIndex :=
  Sum.inr (Sum.inl (monsterNortonOctadIndex 1281 monsterNortonLine01PairUOctad_weight, 45))

/-- The entire physical integer vector of this octad-short output. -/
def monsterNortonLine01PairUShortIntegral : Fin 24 → ℤ :=
  monsterNortonOctadIntegral 1281 monsterNortonLine01PairUOctadPositions 45

/-- The output vector is the actual signed shortest-vector dictionary value. -/
theorem monsterNortonLine01PairUShortIntegral_actual :
    griessShortIntegral monsterNortonLine01PairUShortOutput =
      monsterNortonLine01PairUShortIntegral :=
  monsterNortonOctadIntegral_eq (1281 : Fin 4096) monsterNortonLine01PairUOctad_weight
    monsterNortonLine01PairUOctadPositions monsterNortonLine01PairUOctad_coordinate 45

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual physical coordinates of all sparse second-half input and output short units. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfUData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual source codes of the fourteen input octad blocks. -/
abbrev monsterNortonSecondHalfInputOctadCodes := monsterNortonSecondHalfOctadCode

/-- Genuine weight-eight shape of each input source octad. -/
theorem monsterNortonSecondHalfInputOctad_weight (d : Fin 14) :
    golayMaskWeight (golayEncodedMask (monsterNortonSecondHalfInputOctadCodes d).val) = 8 :=
  monsterNortonSecondHalfOctad_weight d

/-- The sorted physical coordinate supports of all fourteen actual input octads. -/
def monsterNortonSecondHalfInputOctadPositions : Fin 14 → Fin 8 → Fin 24 :=
  ![![8, 9, 10, 11, 12, 13, 14, 15],
    ![4, 5, 6, 7, 12, 13, 14, 15],
    ![4, 5, 6, 7, 8, 9, 10, 11],
    ![1, 3, 5, 7, 9, 11, 13, 15],
    ![1, 3, 5, 7, 8, 10, 12, 14],
    ![1, 3, 4, 6, 9, 11, 12, 14],
    ![1, 3, 4, 6, 8, 10, 13, 15],
    ![0, 1, 2, 3, 8, 9, 10, 11],
    ![0, 1, 2, 3, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7],
    ![0, 2, 5, 7, 8, 10, 13, 15],
    ![0, 2, 5, 7, 9, 11, 12, 14],
    ![0, 2, 4, 6, 8, 10, 12, 14],
    ![0, 2, 4, 6, 9, 11, 13, 15]]

private theorem positions_mem (a : Fin 14) (i : Fin 24) :
    i ∈ golayMaskSupport (golayEncodedMask (monsterNortonSecondHalfInputOctadCodes a).val) ↔
      i ∈ List.ofFn (monsterNortonSecondHalfInputOctadPositions a) := by
  revert a i
  decide +kernel

private theorem positions_sorted (a : Fin 14) :
    List.SortedLT (List.ofFn (monsterNortonSecondHalfInputOctadPositions a)) := by
  revert a
  decide +kernel

private theorem positions_sort (a : Fin 14) :
    (golayMaskSupport (golayEncodedMask (monsterNortonSecondHalfInputOctadCodes a).val)).sort =
      List.ofFn (monsterNortonSecondHalfInputOctadPositions a) := by
  apply (golayMaskSupport _).sortedLT_sort.eq_of_mem_iff (positions_sorted a)
  intro i
  simp only [Finset.mem_sort]
  exact positions_mem a i

private theorem position_index (a : Fin 14) (k : Fin 8) :
    (List.ofFn (monsterNortonSecondHalfInputOctadPositions a)).idxOf
      (monsterNortonSecondHalfInputOctadPositions a k) = k.val := by
  revert a k
  decide +kernel

/-- These finite positions are the actual increasing octad coordinates. -/
theorem monsterNortonSecondHalfInputOctad_coordinate (a : Fin 14) (k : Fin 8) :
    golayOctadCoordinate
      (monsterNortonOctadIndex (monsterNortonSecondHalfInputOctadCodes a)
        (monsterNortonSecondHalfInputOctad_weight a)) k =
          monsterNortonSecondHalfInputOctadPositions a k := by
  apply monsterNortonOctadIndex_coordinate (monsterNortonSecondHalfInputOctadCodes a)
    (monsterNortonSecondHalfInputOctad_weight a) (monsterNortonSecondHalfInputOctadPositions a)
  · intro j
    have h := (positions_mem a (monsterNortonSecondHalfInputOctadPositions a j)).mpr
      (List.mem_ofFn.mpr ⟨j, rfl⟩)
    exact (Finset.mem_filter.mp h).2
  · intro j
    rw [positions_sort]
    exact position_index a j

/-- Exact computable physical input integers for every sparse short unit. -/
def monsterNortonSecondHalfInputIntegral : NortonSecondHalfShortIndex → Fin 24 → ℤ
  | Sum.inl (i, s) => fun j =>
    4 * (if j = monsterNortonSecondHalfPairFirst i then 1 else 0) +
      (if s = 0 then -4 else 4) *
        (if j = monsterNortonSecondHalfPairSecond i then 1 else 0)
  | Sum.inr (d, e) => monsterNortonOctadIntegral (monsterNortonSecondHalfOctadCode d)
      (monsterNortonSecondHalfInputOctadPositions d) (monsterNortonSecondHalfOctadSign d e)

/-- Each finite input formula is the complete actual original Conway shortest-vector dictionary. -/
theorem monsterNortonSecondHalfInputIntegral_actual (i : NortonSecondHalfShortIndex) :
    griessShortIntegral (monsterNortonSecondHalfShortInput i) =
      monsterNortonSecondHalfInputIntegral i := by
  rcases i with ⟨i, s⟩ | ⟨d, e⟩
  · simp only [monsterNortonSecondHalfShortInput, monsterNortonSecondHalfPairIndex,
      griessShortIntegral, griessPairIndex_coordinates, monsterNortonSecondHalfPair_lt,
      ite_true, monsterNortonSecondHalfInputIntegral]
  · exact monsterNortonOctadIntegral_eq _ _ _
      (monsterNortonSecondHalfInputOctad_coordinate d) _

/-- The exact physical integer output formula for every selected actual short label. -/
def monsterNortonSecondHalfOutputIntegral (i : NortonSecondHalfShortIndex) : Fin 24 → ℤ :=
  let k := monsterNortonSecondHalfShortStorage i
  if monsterNortonSecondHalfUKind k = 0 then fun j =>
    4 * (if j = monsterNortonSecondHalfUPairFirst k then 1 else 0) +
      (if monsterNortonSecondHalfUPairSign k = 0 then -4 else 4) *
        (if j = monsterNortonSecondHalfUPairSecond k then 1 else 0)
  else monsterNortonOctadIntegral
    (monsterNortonSecondHalfUOctadCode (monsterNortonSecondHalfUOctadChoice k))
    (monsterNortonSecondHalfUOctadPositions (monsterNortonSecondHalfUOctadChoice k))
    (monsterNortonSecondHalfUOctadSign k)

/-- Every finite output formula equals the complete original physical dictionary vector. -/
theorem monsterNortonSecondHalfOutputIntegral_actual (i : NortonSecondHalfShortIndex) :
    griessShortIntegral (monsterNortonSecondHalfShortUOutput i) =
      monsterNortonSecondHalfOutputIntegral i := by
  unfold monsterNortonSecondHalfShortUOutput monsterNortonSecondHalfOutputIntegral
  by_cases h : monsterNortonSecondHalfUKind (monsterNortonSecondHalfShortStorage i) = 0
  · simp only [h, ite_true, griessShortIntegral, griessPairIndex_coordinates,
      monsterNortonSecondHalfUPair_lt]
  · simp only [h, ite_false]
    exact monsterNortonOctadIntegral_eq _ _ _
      (monsterNortonSecondHalfUOctad_coordinate _) _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

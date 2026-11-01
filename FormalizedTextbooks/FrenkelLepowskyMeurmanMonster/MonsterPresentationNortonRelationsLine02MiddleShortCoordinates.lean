/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The finite middle-short tables are exactly the original pair and octad dictionary. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine02MiddleShortData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000 in
-- Check membership of the thirty explicit source octad supports.
private theorem positions_mem (a : Fin 30) (i : Fin 24) :
    i ∈ golayMaskSupport (golayEncodedMask (monsterNortonLine02MiddleOctadCode a).val) ↔
      i ∈ List.ofFn (monsterNortonLine02MiddleOctadPositions a) := by
  revert a i
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check sortedness of the thirty explicit source octad supports.
private theorem positions_sorted (a : Fin 30) :
    List.SortedLT (List.ofFn (monsterNortonLine02MiddleOctadPositions a)) := by
  revert a
  decide +kernel

private theorem positions_sort (a : Fin 30) :
    (golayMaskSupport (golayEncodedMask (monsterNortonLine02MiddleOctadCode a).val)).sort =
      List.ofFn (monsterNortonLine02MiddleOctadPositions a) := by
  apply (golayMaskSupport _).sortedLT_sort.eq_of_mem_iff (positions_sorted a)
  intro i
  simp only [Finset.mem_sort]
  exact positions_mem a i

private theorem position_index (a : Fin 30) (k : Fin 8) :
    (List.ofFn (monsterNortonLine02MiddleOctadPositions a)).idxOf
      (monsterNortonLine02MiddleOctadPositions a k) = k.val := by
  revert a k
  decide +kernel

/-- These finite positions are the actual increasing octad coordinates. -/
theorem monsterNortonLine02MiddleOctad_coordinate (a : Fin 30) (k : Fin 8) :
    golayOctadCoordinate
      (monsterNortonOctadIndex (monsterNortonLine02MiddleOctadCode a)
        (monsterNortonLine02MiddleOctad_weight a)) k =
          monsterNortonLine02MiddleOctadPositions a k := by
  apply monsterNortonOctadIndex_coordinate (monsterNortonLine02MiddleOctadCode a)
    (monsterNortonLine02MiddleOctad_weight a) (monsterNortonLine02MiddleOctadPositions a)
  · intro j
    have h := (positions_mem a (monsterNortonLine02MiddleOctadPositions a j)).mpr
      (List.mem_ofFn.mpr ⟨j, rfl⟩)
    exact (Finset.mem_filter.mp h).2
  · intro j
    rw [positions_sort]
    exact position_index a j

/-- The whole actual preferred input label at one of the eight middle original basis slots. -/
noncomputable def monsterNortonLine02MiddleInput (a : Fin 8) (e : Fin 64) : GriessShortIndex :=
  Sum.inr (Sum.inl (monsterNortonOctadIndex
    (monsterNortonLine02FirstUOctadCodes (Fin.natAdd 2 (Fin.castAdd 13 a)))
    (monsterNortonLine02FirstUOctad_weight (Fin.natAdd 2 (Fin.castAdd 13 a))), e))

/-- Its displayed integral formula in the actual physical basis. -/
def monsterNortonLine02MiddleInputIntegral (a : Fin 8) (e : Fin 64) : Fin 24 → ℤ :=
  monsterNortonOctadIntegral (monsterNortonLine02FirstUOctadCodes (Fin.natAdd 2 (Fin.castAdd 13 a)))
    (monsterNortonLine02FirstUOctadPositions (Fin.natAdd 2 (Fin.castAdd 13 a))) e

/-- Every stored input formula is the entire actual preferred vector. -/
theorem monsterNortonLine02MiddleInputIntegral_actual (a : Fin 8) (e : Fin 64) :
    griessShortIntegral (monsterNortonLine02MiddleInput a e) =
      monsterNortonLine02MiddleInputIntegral a e :=
  monsterNortonOctadIntegral_eq _ _ _ (monsterNortonLine02FirstUOctad_coordinate _) _

/-- A table entry names an actual preferred original pair or octad label. -/
noncomputable def monsterNortonLine02MiddleOutput (a : Fin 8) (e : Fin 64) : GriessShortIndex :=
  if monsterNortonLine02MiddleOutputKind a e = 0 then
    Sum.inl (monsterNortonLine02MiddlePairSign a e,
      griessPairIndex (monsterNortonLine02MiddlePairFirst a e)
        (monsterNortonLine02MiddlePairSecond a e)
        (ne_of_lt (monsterNortonLine02MiddlePair_lt a e)))
  else Sum.inr (Sum.inl
    (monsterNortonOctadIndex (monsterNortonLine02MiddleOctadCode
      (monsterNortonLine02MiddleOctadChoice a e))
      (monsterNortonLine02MiddleOctad_weight (monsterNortonLine02MiddleOctadChoice a e)),
      monsterNortonLine02MiddleOctadSign a e))

/-- Its computable full physical vector, including every original preferred sign. -/
def monsterNortonLine02MiddleOutputIntegral (a : Fin 8) (e : Fin 64) : Fin 24 → ℤ :=
  if monsterNortonLine02MiddleOutputKind a e = 0 then fun j =>
    4 * (if j = monsterNortonLine02MiddlePairFirst a e then 1 else 0) +
      (if monsterNortonLine02MiddlePairSign a e = 0 then -4 else 4) *
        (if j = monsterNortonLine02MiddlePairSecond a e then 1 else 0)
  else monsterNortonOctadIntegral
    (monsterNortonLine02MiddleOctadCode (monsterNortonLine02MiddleOctadChoice a e))
    (monsterNortonLine02MiddleOctadPositions (monsterNortonLine02MiddleOctadChoice a e))
    (monsterNortonLine02MiddleOctadSign a e)

/-- Every finite output formula is the entire actual original shortest-vector dictionary. -/
theorem monsterNortonLine02MiddleOutputIntegral_actual (a : Fin 8) (e : Fin 64) :
    griessShortIntegral (monsterNortonLine02MiddleOutput a e) =
      monsterNortonLine02MiddleOutputIntegral a e := by
  unfold monsterNortonLine02MiddleOutput monsterNortonLine02MiddleOutputIntegral
  by_cases h : monsterNortonLine02MiddleOutputKind a e = 0
  · simp only [h, ite_true, griessShortIntegral, griessPairIndex_coordinates,
      monsterNortonLine02MiddlePair_lt]
  · simp only [h, ite_false]
    exact monsterNortonOctadIntegral_eq _ _ _
      (monsterNortonLine02MiddleOctad_coordinate _) _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

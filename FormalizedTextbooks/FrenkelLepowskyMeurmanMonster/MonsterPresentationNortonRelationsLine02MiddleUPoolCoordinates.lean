/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual physical dictionary coordinates of the deduplicated middle squared-U pool. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine02MiddleUPoolData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000 in
-- Check membership of the forty-four explicit source octad supports.
private theorem positions_mem (a : Fin 44) (i : Fin 24) :
    i ∈ golayMaskSupport (golayEncodedMask (monsterNortonLine02MiddleUPoolOctadCode a).val) ↔
      i ∈ List.ofFn (monsterNortonLine02MiddleUPoolOctadPositions a) := by
  revert a i
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check sortedness of the forty-four explicit source octad supports.
private theorem positions_sorted (a : Fin 44) :
    List.SortedLT (List.ofFn (monsterNortonLine02MiddleUPoolOctadPositions a)) := by
  revert a
  decide +kernel

private theorem positions_sort (a : Fin 44) :
    (golayMaskSupport (golayEncodedMask (monsterNortonLine02MiddleUPoolOctadCode a).val)).sort =
      List.ofFn (monsterNortonLine02MiddleUPoolOctadPositions a) := by
  apply (golayMaskSupport _).sortedLT_sort.eq_of_mem_iff (positions_sorted a)
  intro i
  simp only [Finset.mem_sort]
  exact positions_mem a i

private theorem position_index (a : Fin 44) (k : Fin 8) :
    (List.ofFn (monsterNortonLine02MiddleUPoolOctadPositions a)).idxOf
      (monsterNortonLine02MiddleUPoolOctadPositions a k) = k.val := by
  revert a k
  decide +kernel

/-- These finite positions are the actual increasing octad coordinates. -/
theorem monsterNortonLine02MiddleUPoolOctad_coordinate (a : Fin 44) (k : Fin 8) :
    golayOctadCoordinate
      (monsterNortonOctadIndex (monsterNortonLine02MiddleUPoolOctadCode a)
        (monsterNortonLine02MiddleUPoolOctad_weight a)) k =
          monsterNortonLine02MiddleUPoolOctadPositions a k := by
  apply monsterNortonOctadIndex_coordinate (monsterNortonLine02MiddleUPoolOctadCode a)
    (monsterNortonLine02MiddleUPoolOctad_weight a) (monsterNortonLine02MiddleUPoolOctadPositions a)
  · intro j
    have h := (positions_mem a (monsterNortonLine02MiddleUPoolOctadPositions a j)).mpr
      (List.mem_ofFn.mpr ⟨j, rfl⟩)
    exact (Finset.mem_filter.mp h).2
  · intro j
    rw [positions_sort]
    exact position_index a j

/-- The whole preferred original short label selected by this finite pool entry. -/
noncomputable def monsterNortonLine02MiddleUPoolInput (i : Fin 1264) : GriessShortIndex :=
  if monsterNortonLine02MiddleUPoolInputKind i = 0 then
    Sum.inl (monsterNortonLine02MiddleUPoolInputPairSign i,
      griessPairIndex (monsterNortonLine02MiddleUPoolInputPairFirst i)
        (monsterNortonLine02MiddleUPoolInputPairSecond i)
        (ne_of_lt (monsterNortonLine02MiddleUPoolInputPair_lt i)))
  else Sum.inr (Sum.inl
    (monsterNortonOctadIndex
      (monsterNortonLine02MiddleUPoolOctadCode (monsterNortonLine02MiddleUPoolInputOctadChoice i))
      (monsterNortonLine02MiddleUPoolOctad_weight
        (monsterNortonLine02MiddleUPoolInputOctadChoice i)),
      monsterNortonLine02MiddleUPoolInputOctadSign i))

/-- The finite whole integer dictionary vector of this actual pool entry. -/
def monsterNortonLine02MiddleUPoolInputIntegral (i : Fin 1264) : Fin 24 → ℤ :=
  if monsterNortonLine02MiddleUPoolInputKind i = 0 then fun j =>
    4 * (if j = monsterNortonLine02MiddleUPoolInputPairFirst i then 1 else 0) +
      (if monsterNortonLine02MiddleUPoolInputPairSign i = 0 then -4 else 4) *
        (if j = monsterNortonLine02MiddleUPoolInputPairSecond i then 1 else 0)
  else monsterNortonOctadIntegral
    (monsterNortonLine02MiddleUPoolOctadCode (monsterNortonLine02MiddleUPoolInputOctadChoice i))
    (monsterNortonLine02MiddleUPoolOctadPositions
      (monsterNortonLine02MiddleUPoolInputOctadChoice i))
    (monsterNortonLine02MiddleUPoolInputOctadSign i)

/-- Every stored physical formula is the entire actual original shortest-vector dictionary. -/
theorem monsterNortonLine02MiddleUPoolInputIntegral_actual (i : Fin 1264) :
    griessShortIntegral (monsterNortonLine02MiddleUPoolInput i) =
      monsterNortonLine02MiddleUPoolInputIntegral i := by
  unfold monsterNortonLine02MiddleUPoolInput monsterNortonLine02MiddleUPoolInputIntegral
  by_cases h : monsterNortonLine02MiddleUPoolInputKind i = 0
  · simp only [h, ite_true, griessShortIntegral, griessPairIndex_coordinates,
      monsterNortonLine02MiddleUPoolInputPair_lt]
  · simp only [h, ite_false]
    exact monsterNortonOctadIntegral_eq _ _ _
      (monsterNortonLine02MiddleUPoolOctad_coordinate _) _

/-- The whole preferred original short label selected by this finite pool entry. -/
noncomputable def monsterNortonLine02MiddleUPoolOutput (i : Fin 1264) : GriessShortIndex :=
  if monsterNortonLine02MiddleUPoolOutputKind i = 0 then
    Sum.inl (monsterNortonLine02MiddleUPoolOutputPairSign i,
      griessPairIndex (monsterNortonLine02MiddleUPoolOutputPairFirst i)
        (monsterNortonLine02MiddleUPoolOutputPairSecond i)
        (ne_of_lt (monsterNortonLine02MiddleUPoolOutputPair_lt i)))
  else Sum.inr (Sum.inl
    (monsterNortonOctadIndex
      (monsterNortonLine02MiddleUPoolOctadCode (monsterNortonLine02MiddleUPoolOutputOctadChoice i))
      (monsterNortonLine02MiddleUPoolOctad_weight
        (monsterNortonLine02MiddleUPoolOutputOctadChoice i)),
      monsterNortonLine02MiddleUPoolOutputOctadSign i))

/-- The finite whole integer dictionary vector of this actual pool entry. -/
def monsterNortonLine02MiddleUPoolOutputIntegral (i : Fin 1264) : Fin 24 → ℤ :=
  if monsterNortonLine02MiddleUPoolOutputKind i = 0 then fun j =>
    4 * (if j = monsterNortonLine02MiddleUPoolOutputPairFirst i then 1 else 0) +
      (if monsterNortonLine02MiddleUPoolOutputPairSign i = 0 then -4 else 4) *
        (if j = monsterNortonLine02MiddleUPoolOutputPairSecond i then 1 else 0)
  else monsterNortonOctadIntegral
    (monsterNortonLine02MiddleUPoolOctadCode (monsterNortonLine02MiddleUPoolOutputOctadChoice i))
    (monsterNortonLine02MiddleUPoolOctadPositions
      (monsterNortonLine02MiddleUPoolOutputOctadChoice i))
    (monsterNortonLine02MiddleUPoolOutputOctadSign i)

/-- Every stored physical formula is the entire actual original shortest-vector dictionary. -/
theorem monsterNortonLine02MiddleUPoolOutputIntegral_actual (i : Fin 1264) :
    griessShortIntegral (monsterNortonLine02MiddleUPoolOutput i) =
      monsterNortonLine02MiddleUPoolOutputIntegral i := by
  unfold monsterNortonLine02MiddleUPoolOutput monsterNortonLine02MiddleUPoolOutputIntegral
  by_cases h : monsterNortonLine02MiddleUPoolOutputKind i = 0
  · simp only [h, ite_true, griessShortIntegral, griessPairIndex_coordinates,
      monsterNortonLine02MiddleUPoolOutputPair_lt]
  · simp only [h, ite_false]
    exact monsterNortonOctadIntegral_eq _ _ _
      (monsterNortonLine02MiddleUPoolOctad_coordinate _) _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

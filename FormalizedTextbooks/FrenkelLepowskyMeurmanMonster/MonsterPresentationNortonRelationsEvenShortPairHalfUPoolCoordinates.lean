/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual physical dictionary coordinates of the deduplicated short U transport pool. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfUPoolData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000 in
-- Check membership of the fifty explicit source octad supports.
private theorem positions_mem (a : Fin 50) (i : Fin 24) :
    i ∈ golayMaskSupport (golayEncodedMask (monsterNortonPairHalfUPoolOctadCode a).val) ↔
      i ∈ List.ofFn (monsterNortonPairHalfUPoolOctadPositions a) := by
  revert a i
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check sortedness of the fifty explicit source octad supports.
private theorem positions_sorted (a : Fin 50) :
    List.SortedLT (List.ofFn (monsterNortonPairHalfUPoolOctadPositions a)) := by
  revert a
  decide +kernel

private theorem positions_sort (a : Fin 50) :
    (golayMaskSupport (golayEncodedMask (monsterNortonPairHalfUPoolOctadCode a).val)).sort =
      List.ofFn (monsterNortonPairHalfUPoolOctadPositions a) := by
  apply (golayMaskSupport _).sortedLT_sort.eq_of_mem_iff (positions_sorted a)
  intro i
  simp only [Finset.mem_sort]
  exact positions_mem a i

private theorem position_index (a : Fin 50) (k : Fin 8) :
    (List.ofFn (monsterNortonPairHalfUPoolOctadPositions a)).idxOf
      (monsterNortonPairHalfUPoolOctadPositions a k) = k.val := by
  revert a k
  decide +kernel

/-- These finite positions are the actual increasing octad coordinates. -/
theorem monsterNortonPairHalfUPoolOctad_coordinate (a : Fin 50) (k : Fin 8) :
    golayOctadCoordinate
      (monsterNortonOctadIndex (monsterNortonPairHalfUPoolOctadCode a)
        (monsterNortonPairHalfUPoolOctad_weight a)) k =
          monsterNortonPairHalfUPoolOctadPositions a k := by
  apply monsterNortonOctadIndex_coordinate (monsterNortonPairHalfUPoolOctadCode a)
    (monsterNortonPairHalfUPoolOctad_weight a) (monsterNortonPairHalfUPoolOctadPositions a)
  · intro j
    have h := (positions_mem a (monsterNortonPairHalfUPoolOctadPositions a j)).mpr
      (List.mem_ofFn.mpr ⟨j, rfl⟩)
    exact (Finset.mem_filter.mp h).2
  · intro j
    rw [positions_sort]
    exact position_index a j

/-- The whole preferred original short label selected by this finite pool entry. -/
noncomputable def monsterNortonPairHalfUPoolInput (i : Fin 1552) : GriessShortIndex :=
  if monsterNortonPairHalfUPoolInputKind i = 0 then
    Sum.inl (monsterNortonPairHalfUPoolInputPairSign i,
      griessPairIndex (monsterNortonPairHalfUPoolInputPairFirst i)
        (monsterNortonPairHalfUPoolInputPairSecond i)
        (ne_of_lt (monsterNortonPairHalfUPoolInputPair_lt i)))
  else Sum.inr (Sum.inl
    (monsterNortonOctadIndex
      (monsterNortonPairHalfUPoolOctadCode (monsterNortonPairHalfUPoolInputOctadChoice i))
      (monsterNortonPairHalfUPoolOctad_weight (monsterNortonPairHalfUPoolInputOctadChoice i)),
      monsterNortonPairHalfUPoolInputOctadSign i))

/-- The finite whole integer dictionary vector of this actual pool entry. -/
def monsterNortonPairHalfUPoolInputIntegral (i : Fin 1552) : Fin 24 → ℤ :=
  if monsterNortonPairHalfUPoolInputKind i = 0 then fun j =>
    4 * (if j = monsterNortonPairHalfUPoolInputPairFirst i then 1 else 0) +
      (if monsterNortonPairHalfUPoolInputPairSign i = 0 then -4 else 4) *
        (if j = monsterNortonPairHalfUPoolInputPairSecond i then 1 else 0)
  else monsterNortonOctadIntegral
    (monsterNortonPairHalfUPoolOctadCode (monsterNortonPairHalfUPoolInputOctadChoice i))
    (monsterNortonPairHalfUPoolOctadPositions (monsterNortonPairHalfUPoolInputOctadChoice i))
    (monsterNortonPairHalfUPoolInputOctadSign i)

/-- Every stored physical formula is the entire actual original shortest-vector dictionary. -/
theorem monsterNortonPairHalfUPoolInputIntegral_actual (i : Fin 1552) :
    griessShortIntegral (monsterNortonPairHalfUPoolInput i) =
      monsterNortonPairHalfUPoolInputIntegral i := by
  unfold monsterNortonPairHalfUPoolInput monsterNortonPairHalfUPoolInputIntegral
  by_cases h : monsterNortonPairHalfUPoolInputKind i = 0
  · simp only [h, ite_true, griessShortIntegral, griessPairIndex_coordinates,
      monsterNortonPairHalfUPoolInputPair_lt]
  · simp only [h, ite_false]
    exact monsterNortonOctadIntegral_eq _ _ _
      (monsterNortonPairHalfUPoolOctad_coordinate _) _

/-- The whole preferred original short label selected by this finite pool entry. -/
noncomputable def monsterNortonPairHalfUPoolOutput (i : Fin 1552) : GriessShortIndex :=
  if monsterNortonPairHalfUPoolOutputKind i = 0 then
    Sum.inl (monsterNortonPairHalfUPoolOutputPairSign i,
      griessPairIndex (monsterNortonPairHalfUPoolOutputPairFirst i)
        (monsterNortonPairHalfUPoolOutputPairSecond i)
        (ne_of_lt (monsterNortonPairHalfUPoolOutputPair_lt i)))
  else Sum.inr (Sum.inl
    (monsterNortonOctadIndex
      (monsterNortonPairHalfUPoolOctadCode (monsterNortonPairHalfUPoolOutputOctadChoice i))
      (monsterNortonPairHalfUPoolOctad_weight (monsterNortonPairHalfUPoolOutputOctadChoice i)),
      monsterNortonPairHalfUPoolOutputOctadSign i))

/-- The finite whole integer dictionary vector of this actual pool entry. -/
def monsterNortonPairHalfUPoolOutputIntegral (i : Fin 1552) : Fin 24 → ℤ :=
  if monsterNortonPairHalfUPoolOutputKind i = 0 then fun j =>
    4 * (if j = monsterNortonPairHalfUPoolOutputPairFirst i then 1 else 0) +
      (if monsterNortonPairHalfUPoolOutputPairSign i = 0 then -4 else 4) *
        (if j = monsterNortonPairHalfUPoolOutputPairSecond i then 1 else 0)
  else monsterNortonOctadIntegral
    (monsterNortonPairHalfUPoolOctadCode (monsterNortonPairHalfUPoolOutputOctadChoice i))
    (monsterNortonPairHalfUPoolOctadPositions (monsterNortonPairHalfUPoolOutputOctadChoice i))
    (monsterNortonPairHalfUPoolOutputOctadSign i)

/-- Every stored physical formula is the entire actual original shortest-vector dictionary. -/
theorem monsterNortonPairHalfUPoolOutputIntegral_actual (i : Fin 1552) :
    griessShortIntegral (monsterNortonPairHalfUPoolOutput i) =
      monsterNortonPairHalfUPoolOutputIntegral i := by
  unfold monsterNortonPairHalfUPoolOutput monsterNortonPairHalfUPoolOutputIntegral
  by_cases h : monsterNortonPairHalfUPoolOutputKind i = 0
  · simp only [h, ite_true, griessShortIntegral, griessPairIndex_coordinates,
      monsterNortonPairHalfUPoolOutputPair_lt]
  · simp only [h, ite_false]
    exact monsterNortonOctadIntegral_eq _ _ _
      (monsterNortonPairHalfUPoolOctad_coordinate _) _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

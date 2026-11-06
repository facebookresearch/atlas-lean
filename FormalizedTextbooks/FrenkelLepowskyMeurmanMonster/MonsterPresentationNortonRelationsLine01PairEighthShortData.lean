/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual finite short-coordinate dictionary for the eighth first-pair word operator. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairSeventhOctadSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairInverseShortData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Source codes of the two original output octads. -/
def monsterNortonLine01PairEighthOctadCodes : Fin 2 → Fin 4096 :=
  ![1281, 3073]

/-- Their genuine increasing physical-coordinate supports. -/
def monsterNortonLine01PairEighthOctadPositions : Fin 2 → Fin 8 → Fin 24 :=
  ![![1, 5, 6, 7, 8, 13, 19, 22],
    ![0, 4, 9, 10, 11, 12, 16, 20]]

/-- Every displayed source code is an actual weight-eight Golay codeword. -/
theorem monsterNortonLine01PairEighthOctad_weight (a : Fin 2) :
    golayMaskWeight (golayEncodedMask (monsterNortonLine01PairEighthOctadCodes a).val) = 8 := by
  revert a
  decide +kernel

private theorem positions_mem (a : Fin 2) (i : Fin 24) :
    i ∈ golayMaskSupport (golayEncodedMask (monsterNortonLine01PairEighthOctadCodes a).val) ↔
      i ∈ List.ofFn (monsterNortonLine01PairEighthOctadPositions a) := by
  revert a i
  decide +kernel

private theorem positions_sorted (a : Fin 2) :
    List.SortedLT (List.ofFn (monsterNortonLine01PairEighthOctadPositions a)) := by
  revert a
  decide +kernel

private theorem positions_sort (a : Fin 2) :
    (golayMaskSupport (golayEncodedMask (monsterNortonLine01PairEighthOctadCodes a).val)).sort =
      List.ofFn (monsterNortonLine01PairEighthOctadPositions a) := by
  apply (golayMaskSupport _).sortedLT_sort.eq_of_mem_iff (positions_sorted a)
  intro i
  simp only [Finset.mem_sort]
  exact positions_mem a i

private theorem position_index (a : Fin 2) (k : Fin 8) :
    (List.ofFn (monsterNortonLine01PairEighthOctadPositions a)).idxOf
      (monsterNortonLine01PairEighthOctadPositions a k) = k.val := by
  revert a k
  decide +kernel

/-- These finite positions are the actual increasing octad coordinates. -/
theorem monsterNortonLine01PairEighthOctad_coordinate (a : Fin 2) (k : Fin 8) :
    golayOctadCoordinate
      (monsterNortonOctadIndex (monsterNortonLine01PairEighthOctadCodes a)
        (monsterNortonLine01PairEighthOctad_weight a)) k =
          monsterNortonLine01PairEighthOctadPositions a k := by
  apply monsterNortonOctadIndex_coordinate (monsterNortonLine01PairEighthOctadCodes a)
    (monsterNortonLine01PairEighthOctad_weight a) (monsterNortonLine01PairEighthOctadPositions a)
  · intro j
    have h := (positions_mem a (monsterNortonLine01PairEighthOctadPositions a j)).mpr
      (List.mem_ofFn.mpr ⟨j, rfl⟩)
    exact (Finset.mem_filter.mp h).2
  · intro j
    rw [positions_sort]
    exact position_index a j

/-- The checked finite ispair field of the actual output dictionary. -/
def monsterNortonLine01PairEighthIsPair : Fin 240 → Bool :=
  ![
    false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, true, false, false, true, true, false, false, true,
    false, true, true, false, false, true, true, false, true, false, false, true,
    true, false, false, true, false, true, true, false, false, true, true, false,
    true, false, false, true, true, false, false, true, false, true, true, false,
    false, true, true, false, false, true, true, false, false, true, true, false,
    true, false, false, true, true, false, false, true, false, true, true, false,
    false, true, true, false, true, false, false, true, true, false, false, true,
    false, true, true, false, false, true, true, false, true, false, false, true,
    true, false, false, true, false, true, true, false, false, true, true, false,
    true, false, false, true, true, false, false, true, true, false, false, true,
    true, false, false, true, false, true, true, false, false, true, true, false,
    true, false, false, true, true, false, false, true, false, true, true, false,
    false, true, true, false, true, false, false, true, true, false, false, true,
    false, true, true, false, false, true, true, false, false, true, true, false,
    false, true, true, false, true, false, false, true, true, false, false, true,
    false, true, true, false, false, true, true, false, true, false, false, true,
    true, false, false, true, false, true, true, false, false, true, true, false,
    true, false, false, true, true, false, false, true, false, true, true, false,
    false, true, true, false, true, false, false, true, true, false, false, true]

/-- The checked finite pairfamily field of the actual output dictionary. -/
def monsterNortonLine01PairEighthPairFamily : Fin 240 → Fin 2 :=
  ![
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1,
    0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0,
    1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0,
    1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1]

/-- The checked finite pairfirst field of the actual output dictionary. -/
def monsterNortonLine01PairEighthPairFirst : Fin 240 → Fin 24 :=
  ![
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 9, 0, 0, 4, 13, 0, 0, 1,
    0, 5, 6, 0, 0, 12, 0, 0, 9, 0, 0, 4,
    13, 0, 0, 1, 0, 5, 7, 0, 0, 12, 0, 0,
    4, 0, 0, 10, 1, 0, 0, 19, 0, 5, 6, 0,
    0, 0, 16, 0, 0, 5, 7, 0, 0, 9, 10, 0,
    11, 0, 0, 0, 6, 0, 0, 1, 0, 9, 10, 0,
    0, 7, 5, 0, 8, 0, 0, 1, 0, 0, 0, 4,
    0, 6, 8, 0, 0, 9, 0, 0, 11, 0, 0, 4,
    5, 0, 0, 1, 0, 0, 10, 0, 0, 8, 6, 0,
    7, 0, 0, 1, 11, 0, 0, 4, 4, 0, 0, 9,
    1, 0, 0, 13, 0, 7, 5, 0, 0, 0, 12, 0,
    10, 0, 0, 4, 19, 0, 0, 1, 0, 6, 5, 0,
    0, 16, 0, 0, 4, 0, 0, 9, 1, 0, 0, 13,
    0, 6, 5, 0, 0, 0, 12, 0, 0, 9, 0, 0,
    0, 6, 8, 0, 5, 0, 0, 1, 11, 0, 0, 4,
    0, 8, 6, 0, 0, 0, 10, 0, 11, 0, 0, 4,
    7, 0, 0, 1, 0, 9, 10, 0, 0, 5, 7, 0,
    6, 0, 0, 1, 11, 0, 0, 0, 0, 7, 5, 0,
    0, 9, 10, 0, 0, 0, 0, 4, 8, 0, 0, 1]

/-- The checked finite pairsecond field of the actual output dictionary. -/
def monsterNortonLine01PairEighthPairSecond : Fin 240 → Fin 24 :=
  ![
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 10, 1, 1, 11, 22, 1, 1, 19,
    1, 7, 8, 1, 1, 20, 16, 1, 11, 1, 1, 10,
    19, 1, 1, 22, 1, 6, 8, 1, 1, 16, 20, 1,
    9, 1, 1, 11, 13, 1, 1, 22, 1, 8, 7, 1,
    1, 12, 20, 1, 1, 13, 22, 1, 1, 12, 20, 1,
    16, 1, 1, 4, 19, 1, 1, 8, 1, 20, 12, 1,
    1, 13, 22, 1, 19, 1, 1, 6, 11, 1, 1, 16,
    1, 13, 22, 1, 1, 16, 10, 1, 12, 1, 1, 20,
    19, 1, 1, 7, 1, 9, 16, 1, 1, 13, 22, 1,
    19, 1, 1, 5, 20, 1, 1, 12, 10, 1, 1, 11,
    22, 1, 1, 19, 1, 8, 6, 1, 1, 20, 16, 1,
    11, 1, 1, 9, 22, 1, 1, 13, 1, 7, 8, 1,
    1, 20, 12, 1, 11, 1, 1, 10, 19, 1, 1, 22,
    1, 8, 7, 1, 1, 16, 20, 1, 1, 16, 10, 1,
    1, 13, 22, 1, 19, 1, 1, 7, 12, 1, 1, 20,
    1, 13, 22, 1, 1, 9, 16, 1, 20, 1, 1, 12,
    19, 1, 1, 5, 1, 12, 20, 1, 1, 13, 22, 1,
    19, 1, 1, 8, 16, 1, 1, 4, 1, 13, 22, 1,
    1, 20, 12, 1, 11, 1, 1, 16, 19, 1, 1, 6]

/-- The checked finite octadslot field of the actual output dictionary. -/
def monsterNortonLine01PairEighthOctadSlot : Fin 240 → Fin 2 :=
  ![
    0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0,
    1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1,
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1,
    0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0,
    0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0,
    0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1,
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0,
    0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0,
    0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0,
    1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0]

/-- The checked finite octadsign field of the actual output dictionary. -/
def monsterNortonLine01PairEighthOctadSign : Fin 240 → Fin 64 :=
  ![
    45, 39, 56, 52, 11, 19, 30, 0, 57, 51, 42, 38,
    13, 21, 30, 0, 0, 1, 31, 0, 0, 20, 10, 0,
    1, 0, 0, 31, 18, 0, 0, 12, 0, 62, 32, 0,
    0, 24, 6, 0, 62, 0, 0, 32, 10, 0, 0, 20,
    0, 44, 50, 0, 0, 25, 7, 0, 42, 0, 0, 52,
    11, 0, 0, 21, 17, 0, 0, 4, 3, 0, 0, 16,
    0, 55, 36, 0, 0, 55, 34, 0, 28, 0, 0, 15,
    27, 0, 0, 14, 0, 35, 54, 0, 0, 54, 37, 0,
    23, 0, 0, 28, 35, 0, 0, 46, 0, 23, 26, 0,
    0, 49, 58, 0, 34, 0, 0, 47, 3, 0, 0, 8,
    0, 59, 48, 0, 0, 8, 5, 0, 0, 51, 45, 0,
    0, 19, 13, 0, 53, 0, 0, 43, 7, 0, 0, 25,
    0, 33, 63, 0, 0, 18, 12, 0, 33, 0, 0, 63,
    6, 0, 0, 24, 0, 43, 53, 0, 0, 44, 50, 0,
    57, 0, 0, 39, 56, 0, 0, 38, 61, 0, 0, 48,
    9, 0, 0, 2, 0, 47, 36, 0, 0, 9, 4, 0,
    29, 0, 0, 22, 60, 0, 0, 49, 0, 22, 27, 0,
    0, 37, 46, 0, 29, 0, 0, 14, 15, 0, 0, 26,
    0, 41, 60, 0, 0, 41, 58, 0, 5, 0, 0, 16,
    2, 0, 0, 17, 0, 40, 59, 0, 0, 61, 40, 0]

/-- The checked finite phase field of the actual output dictionary. -/
def monsterNortonLine01PairEighthPhase : Fin 240 → ZMod 2 :=
  ![
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Every displayed output pair is in the original increasing coordinate convention. -/
theorem monsterNortonLine01PairEighthPair_increasing (k : Fin 240) :
    monsterNortonLine01PairEighthPairFirst k < monsterNortonLine01PairEighthPairSecond k := by
  revert k
  decide +kernel

/-- The genuine original output label for every displayed eighth-step short input. -/
noncomputable def monsterNortonLine01PairEighthShortOutput (k : Fin 240) : GriessShortIndex :=
  if monsterNortonLine01PairEighthIsPair k then
    Sum.inl (monsterNortonLine01PairEighthPairFamily k,
      griessPairIndex (monsterNortonLine01PairEighthPairFirst k)
        (monsterNortonLine01PairEighthPairSecond k)
        (ne_of_lt (monsterNortonLine01PairEighthPair_increasing k)))
  else
    Sum.inr (Sum.inl
      (monsterNortonOctadIndex
        (monsterNortonLine01PairEighthOctadCodes (monsterNortonLine01PairEighthOctadSlot k))
        (monsterNortonLine01PairEighthOctad_weight (monsterNortonLine01PairEighthOctadSlot k)),
          monsterNortonLine01PairEighthOctadSign k))

/-- Its entire finite physical integer vector, for the actual Q conjugation certificates. -/
def monsterNortonLine01PairEighthOutputIntegral (k : Fin 240) : Fin 24 → ℤ :=
  if monsterNortonLine01PairEighthIsPair k then
    fun i => 4 * (if i = monsterNortonLine01PairEighthPairFirst k then 1 else 0) +
      (if monsterNortonLine01PairEighthPairFamily k = 0 then -4 else 4) *
        (if i = monsterNortonLine01PairEighthPairSecond k then 1 else 0)
  else
    monsterNortonOctadIntegral
      (monsterNortonLine01PairEighthOctadCodes (monsterNortonLine01PairEighthOctadSlot k))
      (monsterNortonLine01PairEighthOctadPositions (monsterNortonLine01PairEighthOctadSlot k))
      (monsterNortonLine01PairEighthOctadSign k)

/-- Every finite output vector equals the actual original Conway shortest-vector dictionary. -/
theorem monsterNortonLine01PairEighthOutputIntegral_actual (k : Fin 240) :
    griessShortIntegral (monsterNortonLine01PairEighthShortOutput k) =
      monsterNortonLine01PairEighthOutputIntegral k := by
  unfold monsterNortonLine01PairEighthShortOutput monsterNortonLine01PairEighthOutputIntegral
  by_cases h : monsterNortonLine01PairEighthIsPair k = true
  · simp only [ite_eq_left h, griessShortIntegral, griessPairIndex_coordinates,
      monsterNortonLine01PairEighthPair_increasing, ite_true]
  · simp only [ite_eq_right h]
    exact monsterNortonOctadIntegral_eq
      (monsterNortonLine01PairEighthOctadCodes (monsterNortonLine01PairEighthOctadSlot k))
      (monsterNortonLine01PairEighthOctad_weight (monsterNortonLine01PairEighthOctadSlot k))
      (monsterNortonLine01PairEighthOctadPositions (monsterNortonLine01PairEighthOctadSlot k))
      (monsterNortonLine01PairEighthOctad_coordinate (monsterNortonLine01PairEighthOctadSlot k))
      (monsterNortonLine01PairEighthOctadSign k)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

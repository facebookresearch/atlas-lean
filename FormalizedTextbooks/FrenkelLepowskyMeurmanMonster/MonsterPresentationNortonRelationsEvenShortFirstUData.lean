/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual preferred short labels after the first Norton U on all twenty-three basis units. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortBasisData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual source octad codes; odd-output slots use a weight-eight placeholder. -/
def monsterNortonEvenShortFirstUOctadCodes : Fin 23 → Fin 4096 :=
  ![1281, 1295, 2318, 186, 1467, 1461, 230, 1511, 1513, 2396, 3, 3073,
    186, 3, 3, 3, 384, 304, 448, 288, 320, 272, 3]

/-- Increasing physical supports in the original Conway octad dictionary. -/
def monsterNortonEvenShortFirstUOctadPositions : Fin 23 → Fin 8 → Fin 24 :=
  ![![1, 5, 6, 7, 8, 13, 19, 22],
    ![1, 4, 9, 10, 11, 13, 19, 22],
    ![0, 1, 12, 13, 16, 19, 20, 22],
    ![5, 7, 9, 10, 12, 13, 20, 22],
    ![1, 6, 8, 9, 10, 12, 19, 20],
    ![1, 4, 5, 7, 11, 12, 19, 20],
    ![5, 6, 9, 11, 12, 13, 16, 19],
    ![1, 7, 8, 9, 11, 12, 16, 22],
    ![1, 4, 5, 6, 10, 12, 16, 22],
    ![0, 1, 4, 5, 8, 9, 12, 13],
    ![8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 4, 9, 10, 11, 12, 16, 20],
    ![5, 7, 9, 10, 12, 13, 20, 22],
    ![8, 9, 10, 11, 12, 13, 14, 15],
    ![8, 9, 10, 11, 12, 13, 14, 15],
    ![8, 9, 10, 11, 12, 13, 14, 15],
    ![2, 3, 5, 7, 13, 14, 21, 22],
    ![2, 3, 9, 10, 13, 15, 22, 23],
    ![2, 3, 5, 6, 13, 15, 17, 19],
    ![2, 3, 9, 11, 13, 14, 18, 19],
    ![2, 3, 6, 7, 18, 19, 22, 23],
    ![2, 3, 10, 11, 17, 19, 21, 22],
    ![8, 9, 10, 11, 12, 13, 14, 15]]

/-- Every displayed source code is an actual weight-eight Golay codeword. -/
theorem monsterNortonEvenShortFirstUOctad_weight (a : Fin 23) :
    golayMaskWeight (golayEncodedMask (monsterNortonEvenShortFirstUOctadCodes a).val) = 8 := by
  revert a
  decide +kernel

private theorem positions_mem (a : Fin 23) (i : Fin 24) :
    i ∈ golayMaskSupport (golayEncodedMask (monsterNortonEvenShortFirstUOctadCodes a).val) ↔
      i ∈ List.ofFn (monsterNortonEvenShortFirstUOctadPositions a) := by
  revert a i
  decide +kernel

private theorem positions_sorted (a : Fin 23) :
    List.SortedLT (List.ofFn (monsterNortonEvenShortFirstUOctadPositions a)) := by
  revert a
  decide +kernel

private theorem positions_sort (a : Fin 23) :
    (golayMaskSupport (golayEncodedMask (monsterNortonEvenShortFirstUOctadCodes a).val)).sort =
      List.ofFn (monsterNortonEvenShortFirstUOctadPositions a) := by
  apply (golayMaskSupport _).sortedLT_sort.eq_of_mem_iff (positions_sorted a)
  intro i
  simp only [Finset.mem_sort]
  exact positions_mem a i

private theorem position_index (a : Fin 23) (k : Fin 8) :
    (List.ofFn (monsterNortonEvenShortFirstUOctadPositions a)).idxOf
      (monsterNortonEvenShortFirstUOctadPositions a k) = k.val := by
  revert a k
  decide +kernel

/-- These finite positions are the actual increasing octad coordinates. -/
theorem monsterNortonEvenShortFirstUOctad_coordinate (a : Fin 23) (k : Fin 8) :
    golayOctadCoordinate
      (monsterNortonOctadIndex (monsterNortonEvenShortFirstUOctadCodes a)
        (monsterNortonEvenShortFirstUOctad_weight a)) k =
          monsterNortonEvenShortFirstUOctadPositions a k := by
  apply monsterNortonOctadIndex_coordinate (monsterNortonEvenShortFirstUOctadCodes a)
    (monsterNortonEvenShortFirstUOctad_weight a) (monsterNortonEvenShortFirstUOctadPositions a)
  · intro j
    have h := (positions_mem a (monsterNortonEvenShortFirstUOctadPositions a j)).mpr
      (List.mem_ofFn.mpr ⟨j, rfl⟩)
    exact (Finset.mem_filter.mp h).2
  · intro j
    rw [positions_sort]
    exact position_index a j

/-- The original even-sign labels of the reached octad outputs. -/
def monsterNortonEvenShortFirstUOctadSign : Fin 23 → Fin 64 :=
  ![45, 57, 15, 58, 51, 57, 58, 51, 57, 60, 0, 57, 16, 0, 0, 0, 35, 28, 35, 35, 44, 19, 0]

/-- Which reached units use the genuine odd-coordinate summand. -/
def monsterNortonEvenShortFirstUIsOdd (k : Fin 23) : Bool :=
  k.val = 10 || k.val = 13 || k.val = 14 || k.val = 15 || k.val = 22

/-- Actual source Golay codes for the five odd outputs. -/
def monsterNortonEvenShortFirstUOddCode : Fin 23 → Fin 2048 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 338, 0, 0, 948, 744, 692, 0, 0, 0, 0, 0, 0, 1024]

/-- Original distinguished physical positions for those odd outputs. -/
def monsterNortonEvenShortFirstUOddPosition : Fin 23 → Fin 24 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 2, 2, 0, 0, 0, 0, 0, 0, 13]

/-- The actual original short-coordinate label after the first U operator. -/
noncomputable def monsterNortonEvenShortFirstUOutput (k : Fin 23) : GriessShortIndex :=
  if monsterNortonEvenShortFirstUIsOdd k then
    Sum.inr (Sum.inr (monsterNortonEvenShortFirstUOddCode k,
      monsterNortonEvenShortFirstUOddPosition k))
  else
    Sum.inr (Sum.inl (monsterNortonOctadIndex (monsterNortonEvenShortFirstUOctadCodes k)
      (monsterNortonEvenShortFirstUOctad_weight k), monsterNortonEvenShortFirstUOctadSign k))

/-- Complete finite physical integer vectors for these preferred outputs. -/
def monsterNortonEvenShortFirstUIntegral (k : Fin 23) : Fin 24 → ℤ :=
  if monsterNortonEvenShortFirstUIsOdd k then
    fun i => (if (golayEncodedMask (monsterNortonEvenShortFirstUOddCode k).val).testBit i.val
      then -1 else 1) * (if i = monsterNortonEvenShortFirstUOddPosition k then -3 else 1)
  else
    monsterNortonOctadIntegral (monsterNortonEvenShortFirstUOctadCodes k)
      (monsterNortonEvenShortFirstUOctadPositions k) (monsterNortonEvenShortFirstUOctadSign k)

/-- All finite output vectors agree with the original physical Conway dictionary. -/
theorem monsterNortonEvenShortFirstUIntegral_actual (k : Fin 23) :
    griessShortIntegral (monsterNortonEvenShortFirstUOutput k) =
      monsterNortonEvenShortFirstUIntegral k := by
  unfold monsterNortonEvenShortFirstUOutput monsterNortonEvenShortFirstUIntegral
  by_cases h : monsterNortonEvenShortFirstUIsOdd k = true
  · simp only [ite_eq_left h]
    rfl
  · simp only [ite_eq_right h]
    exact monsterNortonOctadIntegral_eq (monsterNortonEvenShortFirstUOctadCodes k)
      (monsterNortonEvenShortFirstUOctad_weight k) (monsterNortonEvenShortFirstUOctadPositions k)
      (monsterNortonEvenShortFirstUOctad_coordinate k) (monsterNortonEvenShortFirstUOctadSign k)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

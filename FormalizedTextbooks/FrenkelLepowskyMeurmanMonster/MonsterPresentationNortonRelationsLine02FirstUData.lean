/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual preferred short labels after the first squared Norton U on all twenty-three basis
  units. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortBasisData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual source octad codes; odd-output slots use a weight-eight placeholder. -/
def monsterNortonLine02FirstUOctadCodes : Fin 23 → Fin 4096 :=
  ![3, 3, 284, 2678, 875, 3946, 2922, 3702, 631, 3073, 2049, 3, 3, 3, 3, 3, 96, 74, 70, 112,
    128, 192, 3]

/-- Increasing physical supports in the original Conway octad dictionary. -/
def monsterNortonLine02FirstUOctadPositions : Fin 23 → Fin 8 → Fin 24 :=
  ![![8, 9, 10, 11, 12, 13, 14, 15],
    ![8, 9, 10, 11, 12, 13, 14, 15],
    ![2, 3, 10, 11, 16, 18, 20, 23],
    ![0, 2, 4, 5, 8, 11, 20, 23],
    ![1, 2, 4, 5, 9, 11, 16, 18],
    ![0, 1, 2, 5, 10, 12, 18, 20],
    ![0, 3, 4, 5, 8, 10, 16, 18],
    ![0, 1, 3, 5, 11, 12, 16, 23],
    ![1, 3, 4, 5, 9, 10, 20, 23],
    ![0, 4, 9, 10, 11, 12, 16, 20],
    ![0, 1, 2, 3, 8, 9, 10, 11],
    ![8, 9, 10, 11, 12, 13, 14, 15],
    ![8, 9, 10, 11, 12, 13, 14, 15],
    ![8, 9, 10, 11, 12, 13, 14, 15],
    ![8, 9, 10, 11, 12, 13, 14, 15],
    ![8, 9, 10, 11, 12, 13, 14, 15],
    ![6, 7, 9, 11, 13, 14, 22, 23],
    ![6, 7, 12, 13, 17, 19, 20, 23],
    ![6, 7, 12, 13, 16, 18, 21, 22],
    ![6, 7, 9, 10, 13, 15, 18, 19],
    ![5, 7, 13, 15, 17, 18, 22, 23],
    ![5, 6, 13, 14, 18, 19, 21, 23],
    ![8, 9, 10, 11, 12, 13, 14, 15]]

/-- Every displayed source code is an actual weight-eight Golay codeword. -/
theorem monsterNortonLine02FirstUOctad_weight (a : Fin 23) :
    golayMaskWeight (golayEncodedMask (monsterNortonLine02FirstUOctadCodes a).val) = 8 := by
  revert a
  decide +kernel

private theorem positions_mem (a : Fin 23) (i : Fin 24) :
    i ∈ golayMaskSupport (golayEncodedMask (monsterNortonLine02FirstUOctadCodes a).val) ↔
      i ∈ List.ofFn (monsterNortonLine02FirstUOctadPositions a) := by
  revert a i
  decide +kernel

private theorem positions_sorted (a : Fin 23) :
    List.SortedLT (List.ofFn (monsterNortonLine02FirstUOctadPositions a)) := by
  revert a
  decide +kernel

private theorem positions_sort (a : Fin 23) :
    (golayMaskSupport (golayEncodedMask (monsterNortonLine02FirstUOctadCodes a).val)).sort =
      List.ofFn (monsterNortonLine02FirstUOctadPositions a) := by
  apply (golayMaskSupport _).sortedLT_sort.eq_of_mem_iff (positions_sorted a)
  intro i
  simp only [Finset.mem_sort]
  exact positions_mem a i

private theorem position_index (a : Fin 23) (k : Fin 8) :
    (List.ofFn (monsterNortonLine02FirstUOctadPositions a)).idxOf
      (monsterNortonLine02FirstUOctadPositions a k) = k.val := by
  revert a k
  decide +kernel

/-- These finite positions are the actual increasing octad coordinates. -/
theorem monsterNortonLine02FirstUOctad_coordinate (a : Fin 23) (k : Fin 8) :
    golayOctadCoordinate
      (monsterNortonOctadIndex (monsterNortonLine02FirstUOctadCodes a)
        (monsterNortonLine02FirstUOctad_weight a)) k =
          monsterNortonLine02FirstUOctadPositions a k := by
  apply monsterNortonOctadIndex_coordinate (monsterNortonLine02FirstUOctadCodes a)
    (monsterNortonLine02FirstUOctad_weight a) (monsterNortonLine02FirstUOctadPositions a)
  · intro j
    have h := (positions_mem a (monsterNortonLine02FirstUOctadPositions a j)).mpr
      (List.mem_ofFn.mpr ⟨j, rfl⟩)
    exact (Finset.mem_filter.mp h).2
  · intro j
    rw [positions_sort]
    exact position_index a j

/-- The original even-sign labels of the reached octad outputs. -/
def monsterNortonLine02FirstUOctadSign : Fin 23 → Fin 64 :=
  ![0, 0, 15, 46, 46, 60, 46, 60, 46, 58, 51, 0, 0, 0, 0, 0, 35, 55, 40, 28, 26, 42, 0]

/-- Which reached units use the genuine odd-coordinate summand. -/
def monsterNortonLine02FirstUIsOdd (k : Fin 23) : Bool :=
  k.val = 0 || k.val = 1 || k.val = 11 || k.val = 12 || k.val = 13 || k.val = 14 || k.val =
    15 || k.val = 22

/-- Actual source Golay codes for the eight odd outputs. -/
def monsterNortonLine02FirstUOddCode : Fin 23 → Fin 2048 :=
  ![285, 285, 0, 0, 0, 0, 0, 0, 0, 0, 0, 349, 548, 1832, 553, 821, 0, 0, 0, 0, 0, 0, 1039]

/-- Original distinguished physical positions for those odd outputs. -/
def monsterNortonLine02FirstUOddPosition : Fin 23 → Fin 24 :=
  ![7, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 13, 13, 13, 13, 0, 0, 0, 0, 0, 0, 13]

/-- The actual original short-coordinate label after the first squared U operator. -/
noncomputable def monsterNortonLine02FirstUOutput (k : Fin 23) : GriessShortIndex :=
  if monsterNortonLine02FirstUIsOdd k then
    Sum.inr (Sum.inr (monsterNortonLine02FirstUOddCode k,
      monsterNortonLine02FirstUOddPosition k))
  else
    Sum.inr (Sum.inl (monsterNortonOctadIndex (monsterNortonLine02FirstUOctadCodes k)
      (monsterNortonLine02FirstUOctad_weight k), monsterNortonLine02FirstUOctadSign k))

/-- Complete finite physical integer vectors for these preferred outputs. -/
def monsterNortonLine02FirstUIntegral (k : Fin 23) : Fin 24 → ℤ :=
  if monsterNortonLine02FirstUIsOdd k then
    fun i => (if (golayEncodedMask (monsterNortonLine02FirstUOddCode k).val).testBit i.val
      then -1 else 1) * (if i = monsterNortonLine02FirstUOddPosition k then -3 else 1)
  else
    monsterNortonOctadIntegral (monsterNortonLine02FirstUOctadCodes k)
      (monsterNortonLine02FirstUOctadPositions k) (monsterNortonLine02FirstUOctadSign k)

/-- All finite output vectors agree with the original physical Conway dictionary. -/
theorem monsterNortonLine02FirstUIntegral_actual (k : Fin 23) :
    griessShortIntegral (monsterNortonLine02FirstUOutput k) =
      monsterNortonLine02FirstUIntegral k := by
  unfold monsterNortonLine02FirstUOutput monsterNortonLine02FirstUIntegral
  by_cases h : monsterNortonLine02FirstUIsOdd k = true
  · simp only [ite_eq_left h]
    rfl
  · simp only [ite_eq_right h]
    exact monsterNortonOctadIntegral_eq (monsterNortonLine02FirstUOctadCodes k)
      (monsterNortonLine02FirstUOctad_weight k) (monsterNortonLine02FirstUOctadPositions k)
      (monsterNortonLine02FirstUOctad_coordinate k) (monsterNortonLine02FirstUOctadSign k)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

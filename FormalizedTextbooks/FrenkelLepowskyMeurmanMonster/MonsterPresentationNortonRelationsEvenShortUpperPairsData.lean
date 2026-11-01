/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual opposite-family pair inputs and their exact source U output dictionaries. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairInverseThird
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUInversePhysicalCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The eleven actual opposite-family inputs at the original physical pair coordinates. -/
noncomputable def monsterNortonEvenShortUpperInput (k : Fin 11) : GriessShortIndex :=
  Sum.inl (1, monsterNortonEvenShortPairIndex k)

/-- Their complete integer dictionary vectors are positive at both original pair coordinates. -/
def monsterNortonEvenShortUpperInputIntegral (k : Fin 11) (i : Fin 24) : ℤ :=
  4 * (if i = 0 then 1 else 0) +
    4 * (if i = monsterNortonEvenShortPairCoordinate k then 1 else 0)

/-- These finite formulas are the actual original preferred shortest-vector inputs. -/
theorem monsterNortonEvenShortUpperInputIntegral_actual (k : Fin 11) :
    griessShortIntegral (monsterNortonEvenShortUpperInput k) =
      monsterNortonEvenShortUpperInputIntegral k := by
  simp only [monsterNortonEvenShortUpperInput, monsterNortonEvenShortPairIndex,
    griessShortIntegral, griessPairIndex_coordinates,
    monsterNortonEvenShortPairCoordinate_positive, ite_true,
    show (1 : Fin 2) ≠ 0 by decide, ite_false]
  rfl

/-- Actual source octad codes, with one weight-eight placeholder at the true odd output. -/
def monsterNortonEvenShortUpperUOctadCodes : Fin 11 → Fin 4096 :=
  ![3073, 3087, 14, 2490, 3259, 3253, 2534, 3303, 3305, 92, 3]

/-- Increasing physical supports in the original source dictionary. -/
def monsterNortonEvenShortUpperUOctadPositions : Fin 11 → Fin 8 → Fin 24 :=
  ![![0, 4, 9, 10, 11, 12, 16, 20],
    ![0, 5, 6, 7, 8, 12, 16, 20],
    ![4, 5, 6, 7, 8, 9, 10, 11],
    ![0, 1, 4, 6, 8, 11, 16, 19],
    ![0, 4, 5, 7, 11, 13, 16, 22],
    ![0, 6, 8, 9, 10, 13, 16, 22],
    ![0, 1, 4, 7, 8, 10, 20, 22],
    ![0, 4, 5, 6, 10, 13, 19, 20],
    ![0, 7, 8, 9, 11, 13, 19, 20],
    ![6, 7, 10, 11, 16, 19, 20, 22],
    ![8, 9, 10, 11, 12, 13, 14, 15]]

/-- Every displayed source octad code has genuine weight eight. -/
theorem monsterNortonEvenShortUpperUOctad_weight (k : Fin 11) :
    golayMaskWeight (golayEncodedMask (monsterNortonEvenShortUpperUOctadCodes k).val) = 8 := by
  revert k
  decide +kernel

private theorem positions_mem (a : Fin 11) (i : Fin 24) :
    i ∈ golayMaskSupport (golayEncodedMask (monsterNortonEvenShortUpperUOctadCodes a).val) ↔
      i ∈ List.ofFn (monsterNortonEvenShortUpperUOctadPositions a) := by
  revert a i
  decide +kernel

private theorem positions_sorted (a : Fin 11) :
    List.SortedLT (List.ofFn (monsterNortonEvenShortUpperUOctadPositions a)) := by
  revert a
  decide +kernel

private theorem positions_sort (a : Fin 11) :
    (golayMaskSupport (golayEncodedMask (monsterNortonEvenShortUpperUOctadCodes a).val)).sort =
      List.ofFn (monsterNortonEvenShortUpperUOctadPositions a) := by
  apply (golayMaskSupport _).sortedLT_sort.eq_of_mem_iff (positions_sorted a)
  intro i
  simp only [Finset.mem_sort]
  exact positions_mem a i

private theorem position_index (a : Fin 11) (k : Fin 8) :
    (List.ofFn (monsterNortonEvenShortUpperUOctadPositions a)).idxOf
      (monsterNortonEvenShortUpperUOctadPositions a k) = k.val := by
  revert a k
  decide +kernel

/-- These finite positions are the actual increasing octad coordinates. -/
theorem monsterNortonEvenShortUpperUOctad_coordinate (a : Fin 11) (k : Fin 8) :
    golayOctadCoordinate
      (monsterNortonOctadIndex (monsterNortonEvenShortUpperUOctadCodes a)
        (monsterNortonEvenShortUpperUOctad_weight a)) k =
          monsterNortonEvenShortUpperUOctadPositions a k := by
  apply monsterNortonOctadIndex_coordinate (monsterNortonEvenShortUpperUOctadCodes a)
    (monsterNortonEvenShortUpperUOctad_weight a) (monsterNortonEvenShortUpperUOctadPositions a)
  · intro j
    have h := (positions_mem a (monsterNortonEvenShortUpperUOctadPositions a j)).mpr
      (List.mem_ofFn.mpr ⟨j, rfl⟩)
    exact (Finset.mem_filter.mp h).2
  · intro j
    rw [positions_sort]
    exact position_index a j

/-- Actual even-sign labels of the ten original octad outputs. -/
def monsterNortonEvenShortUpperUOctadSign : Fin 11 → Fin 64 :=
  ![57, 45, 51, 43, 57, 51, 43, 57, 51, 15, 0]

/-- The final physical pair has a genuine odd-family output. -/
def monsterNortonEvenShortUpperUIsOdd (k : Fin 11) : Bool := k.val = 10

/-- Complete preferred labels of the actual source output dictionaries. -/
noncomputable def monsterNortonEvenShortUpperUOutput (k : Fin 11) : GriessShortIndex :=
  if monsterNortonEvenShortUpperUIsOdd k then Sum.inr (Sum.inr (82, 3)) else
    Sum.inr (Sum.inl (monsterNortonOctadIndex (monsterNortonEvenShortUpperUOctadCodes k)
      (monsterNortonEvenShortUpperUOctad_weight k), monsterNortonEvenShortUpperUOctadSign k))

/-- Finite integer output coordinates, including the actual odd source branch. -/
def monsterNortonEvenShortUpperUIntegral (k : Fin 11) : Fin 24 → ℤ :=
  if monsterNortonEvenShortUpperUIsOdd k then fun i =>
    (if (golayEncodedMask 82).testBit i.val then -1 else 1) * (if i = 3 then -3 else 1)
  else monsterNortonOctadIntegral (monsterNortonEvenShortUpperUOctadCodes k)
    (monsterNortonEvenShortUpperUOctadPositions k) (monsterNortonEvenShortUpperUOctadSign k)

/-- Every output formula equals its entire actual original physical dictionary vector. -/
theorem monsterNortonEvenShortUpperUIntegral_actual (k : Fin 11) :
    griessShortIntegral (monsterNortonEvenShortUpperUOutput k) =
      monsterNortonEvenShortUpperUIntegral k := by
  unfold monsterNortonEvenShortUpperUOutput monsterNortonEvenShortUpperUIntegral
  by_cases h : monsterNortonEvenShortUpperUIsOdd k = true
  · simp only [h, ite_true]
    rfl
  · simp only [h]
    exact monsterNortonOctadIntegral_eq _ _ _
      (monsterNortonEvenShortUpperUOctad_coordinate k) _

/-- Exact finite hyperbolic masks of the original opposite-family inputs. -/
def monsterNortonEvenShortUpperUMask : Fin 11 → ℕ :=
  ![6293504, 5244928, 7342080, 4257792, 587776, 325632, 4253696, 190464, 124928, 4249600, 4241408]

/-- Global shortest-vector representative signs of the physical U action. -/
def monsterNortonEvenShortUpperUPhysicalSign : Fin 11 → ℤ :=
  ![-1, -1, 1, -1, -1, -1, -1, -1, -1, -1, 1]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

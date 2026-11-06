/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual even-short labels for a basis of the first twenty-three Q coordinates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Source codes of the eleven actual basis octads. -/
def monsterNortonEvenShortOctadCodes : Fin 11 → Fin 4096 :=
  ![3, 5, 7, 9, 16, 32, 64, 128, 256, 512, 1024]

/-- Increasing physical supports of those original Golay octads. -/
def monsterNortonEvenShortOctadPositions : Fin 11 → Fin 8 → Fin 24 :=
  ![![8, 9, 10, 11, 12, 13, 14, 15],
    ![8, 9, 10, 11, 16, 17, 18, 19],
    ![4, 5, 6, 7, 20, 21, 22, 23],
    ![8, 9, 10, 11, 20, 21, 22, 23],
    ![10, 11, 14, 15, 18, 19, 22, 23],
    ![9, 11, 13, 15, 17, 19, 21, 23],
    ![6, 7, 14, 15, 17, 19, 21, 22],
    ![5, 7, 13, 15, 17, 18, 22, 23],
    ![2, 3, 14, 15, 17, 18, 21, 23],
    ![1, 3, 13, 15, 18, 19, 21, 22],
    ![1, 2, 3, 4, 8, 12, 16, 20]]

/-- Every displayed source code is an actual weight-eight Golay codeword. -/
theorem monsterNortonEvenShortOctad_weight (a : Fin 11) :
    golayMaskWeight (golayEncodedMask (monsterNortonEvenShortOctadCodes a).val) = 8 := by
  revert a
  decide +kernel

private theorem positions_mem (a : Fin 11) (i : Fin 24) :
    i ∈ golayMaskSupport (golayEncodedMask (monsterNortonEvenShortOctadCodes a).val) ↔
      i ∈ List.ofFn (monsterNortonEvenShortOctadPositions a) := by
  revert a i
  decide +kernel

private theorem positions_sorted (a : Fin 11) :
    List.SortedLT (List.ofFn (monsterNortonEvenShortOctadPositions a)) := by
  revert a
  decide +kernel

private theorem positions_sort (a : Fin 11) :
    (golayMaskSupport (golayEncodedMask (monsterNortonEvenShortOctadCodes a).val)).sort =
      List.ofFn (monsterNortonEvenShortOctadPositions a) := by
  apply (golayMaskSupport _).sortedLT_sort.eq_of_mem_iff (positions_sorted a)
  intro i
  simp only [Finset.mem_sort]
  exact positions_mem a i

private theorem position_index (a : Fin 11) (k : Fin 8) :
    (List.ofFn (monsterNortonEvenShortOctadPositions a)).idxOf
      (monsterNortonEvenShortOctadPositions a k) = k.val := by
  revert a k
  decide +kernel

/-- These finite positions are the actual increasing octad coordinates. -/
theorem monsterNortonEvenShortOctad_coordinate (a : Fin 11) (k : Fin 8) :
    golayOctadCoordinate
      (monsterNortonOctadIndex (monsterNortonEvenShortOctadCodes a)
        (monsterNortonEvenShortOctad_weight a)) k =
          monsterNortonEvenShortOctadPositions a k := by
  apply monsterNortonOctadIndex_coordinate (monsterNortonEvenShortOctadCodes a)
    (monsterNortonEvenShortOctad_weight a) (monsterNortonEvenShortOctadPositions a)
  · intro j
    have h := (positions_mem a (monsterNortonEvenShortOctadPositions a j)).mpr
      (List.mem_ofFn.mpr ⟨j, rfl⟩)
    exact (Finset.mem_filter.mp h).2
  · intro j
    rw [positions_sort]
    exact position_index a j

/-- The twelve actual signed-pair second coordinates. -/
def monsterNortonEvenShortPairSecond : Fin 12 → Fin 24 :=
  ![1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 1]

/-- Each chosen second coordinate is distinct from the first physical coordinate zero. -/
theorem monsterNortonEvenShortPairSecond_positive (k : Fin 12) :
    0 < monsterNortonEvenShortPairSecond k := by
  revert k
  decide +kernel

/-- Twenty-three genuine preferred short labels, twelve pairs and eleven octads. -/
noncomputable def monsterNortonEvenShortBasis (k : Fin 23) : GriessShortIndex :=
  if hk : k.val < 12 then
    let j : Fin 12 := ⟨k.val, hk⟩
    Sum.inl ((if j.val = 11 then 1 else 0),
      griessPairIndex 0 (monsterNortonEvenShortPairSecond j)
        (ne_of_lt (monsterNortonEvenShortPairSecond_positive j)))
  else
    let j : Fin 11 := ⟨k.val - 12, by omega⟩
    Sum.inr (Sum.inl
      (monsterNortonOctadIndex (monsterNortonEvenShortOctadCodes j)
        (monsterNortonEvenShortOctad_weight j), 0))

/-- Their complete finite physical integer vectors in the actual shortest-vector dictionary. -/
def monsterNortonEvenShortIntegral (k : Fin 23) : Fin 24 → ℤ :=
  if hk : k.val < 12 then
    let j : Fin 12 := ⟨k.val, hk⟩
    fun i => 4 * (if i = 0 then 1 else 0) +
      (if j.val = 11 then 4 else -4) *
        (if i = monsterNortonEvenShortPairSecond j then 1 else 0)
  else
    let j : Fin 11 := ⟨k.val - 12, by omega⟩
    monsterNortonOctadIntegral (monsterNortonEvenShortOctadCodes j)
      (monsterNortonEvenShortOctadPositions j) 0

/-- The finite vectors are exactly the actual original Conway short coordinates. -/
theorem monsterNortonEvenShortIntegral_actual (k : Fin 23) :
    griessShortIntegral (monsterNortonEvenShortBasis k) = monsterNortonEvenShortIntegral k := by
  unfold monsterNortonEvenShortBasis monsterNortonEvenShortIntegral
  by_cases hk : k.val < 12
  · simp only [dite_eq_left hk]
    rw [griessShortIntegral, griessPairIndex_coordinates]
    simp only [show (0 : Fin 24) < monsterNortonEvenShortPairSecond ⟨k.val, hk⟩ from
      monsterNortonEvenShortPairSecond_positive _, ite_true]
    funext i
    by_cases h : k.val = 11 <;> simp [h]
  · simp only [dite_eq_right hk]
    exact monsterNortonOctadIntegral_eq
      (monsterNortonEvenShortOctadCodes ⟨k.val - 12, by omega⟩)
      (monsterNortonEvenShortOctad_weight ⟨k.val - 12, by omega⟩)
      (monsterNortonEvenShortOctadPositions ⟨k.val - 12, by omega⟩)
      (monsterNortonEvenShortOctad_coordinate ⟨k.val - 12, by omega⟩) 0

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

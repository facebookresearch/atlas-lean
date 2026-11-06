/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual short labels for inverse U on the first reached sixty-four-sign octad. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairShortData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual source codes of the fourteen inverse-image octads. -/
def monsterNortonLine01PairInverseOctadCodes : Fin 14 → Fin 4096 :=
  ![3, 13, 14, 336, 339, 349, 350, 2049, 2050, 2063, 2385, 2386, 2396, 2399]

/-- The finite pair-versus-octad tag of each inverse image. -/
def monsterNortonLine01PairInverseIsPair : Fin 64 → Bool :=
  ![
    true, false, false, false, false, false, false, false,
    false, false, false, true, false, false, false, false,
    false, false, false, false, false, true, false, false,
    false, false, false, false, false, false, true, false,
    false, false, false, false, false, false, true, false,
    false, false, false, false, false, true, false, false,
    false, false, false, true, false, false, false, false,
    true, false, false, false, false, false, false, false]

/-- The original pair family of each inverse pair image. -/
def monsterNortonLine01PairInversePairSign : Fin 64 → Fin 2 :=
  ![
    1, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- The first physical coordinate of each inverse pair image. -/
def monsterNortonLine01PairInversePairFirst : Fin 64 → Fin 24 :=
  ![
    14, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 8, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 10, 0, 0,
    0, 0, 0, 0, 0, 0, 12, 0,
    0, 0, 0, 0, 0, 0, 6, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 2, 0, 0, 0, 0,
    4, 0, 0, 0, 0, 0, 0, 0]

/-- The second physical coordinate of each inverse pair image. -/
def monsterNortonLine01PairInversePairSecond : Fin 64 → Fin 24 :=
  ![
    15, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 9, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 11, 1, 1,
    1, 1, 1, 1, 1, 1, 13, 1,
    1, 1, 1, 1, 1, 1, 7, 1,
    1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 3, 1, 1, 1, 1,
    5, 1, 1, 1, 1, 1, 1, 1]

/-- The source-octad slot of each inverse image. -/
def monsterNortonLine01PairInverseOctadSlot : Fin 64 → Fin 14 :=
  ![
    0, 0, 10, 6, 3, 13, 1, 2,
    6, 10, 0, 0, 8, 7, 4, 12,
    13, 3, 8, 7, 0, 0, 11, 5,
    1, 2, 12, 4, 5, 11, 0, 0,
    1, 8, 3, 4, 10, 11, 0, 9,
    13, 12, 2, 7, 9, 0, 11, 10,
    6, 5, 9, 0, 2, 7, 4, 3,
    0, 9, 5, 6, 12, 13, 1, 8]

/-- The original even local sign label of each inverse octad image. -/
def monsterNortonLine01PairInverseOctadSign : Fin 64 → Fin 64 :=
  ![
    0, 33, 30, 20, 15, 5, 29, 29,
    27, 17, 29, 0, 29, 29, 31, 21,
    10, 0, 18, 18, 18, 0, 14, 4,
    18, 18, 26, 16, 11, 1, 0, 46,
    46, 33, 60, 35, 45, 50, 0, 46,
    57, 38, 33, 46, 18, 0, 61, 34,
    40, 55, 29, 0, 46, 33, 44, 51,
    0, 33, 56, 39, 41, 54, 33, 46]

/-- Increasing physical positions in the fourteen actual inverse-image octads. -/
def monsterNortonLine01PairInverseOctadPositions : Fin 14 → Fin 8 → Fin 24 :=
  ![![8, 9, 10, 11, 12, 13, 14, 15],
    ![4, 5, 6, 7, 12, 13, 14, 15],
    ![4, 5, 6, 7, 8, 9, 10, 11],
    ![2, 3, 6, 7, 10, 11, 14, 15],
    ![2, 3, 6, 7, 8, 9, 12, 13],
    ![2, 3, 4, 5, 10, 11, 12, 13],
    ![2, 3, 4, 5, 8, 9, 14, 15],
    ![0, 1, 2, 3, 8, 9, 10, 11],
    ![0, 1, 2, 3, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7],
    ![0, 1, 6, 7, 8, 9, 14, 15],
    ![0, 1, 6, 7, 10, 11, 12, 13],
    ![0, 1, 4, 5, 8, 9, 12, 13],
    ![0, 1, 4, 5, 10, 11, 14, 15]]

/-- Every displayed source code is an actual weight-eight Golay codeword. -/
theorem monsterNortonLine01PairInverseOctad_weight (a : Fin 14) :
    golayMaskWeight (golayEncodedMask (monsterNortonLine01PairInverseOctadCodes a).val) = 8 := by
  revert a
  decide +kernel

private theorem positions_mem (a : Fin 14) (i : Fin 24) :
    i ∈ golayMaskSupport (golayEncodedMask (monsterNortonLine01PairInverseOctadCodes a).val) ↔
      i ∈ List.ofFn (monsterNortonLine01PairInverseOctadPositions a) := by
  revert a i
  decide +kernel

private theorem positions_sorted (a : Fin 14) :
    List.SortedLT (List.ofFn (monsterNortonLine01PairInverseOctadPositions a)) := by
  revert a
  decide +kernel

private theorem positions_sort (a : Fin 14) :
    (golayMaskSupport (golayEncodedMask (monsterNortonLine01PairInverseOctadCodes a).val)).sort =
      List.ofFn (monsterNortonLine01PairInverseOctadPositions a) := by
  apply (golayMaskSupport _).sortedLT_sort.eq_of_mem_iff (positions_sorted a)
  intro i
  simp only [Finset.mem_sort]
  exact positions_mem a i

private theorem position_index (a : Fin 14) (k : Fin 8) :
    (List.ofFn (monsterNortonLine01PairInverseOctadPositions a)).idxOf
      (monsterNortonLine01PairInverseOctadPositions a k) = k.val := by
  revert a k
  decide +kernel

/-- These finite positions are the actual increasing octad coordinates. -/
theorem monsterNortonLine01PairInverseOctad_coordinate (a : Fin 14) (k : Fin 8) :
    golayOctadCoordinate
      (monsterNortonOctadIndex (monsterNortonLine01PairInverseOctadCodes a)
        (monsterNortonLine01PairInverseOctad_weight a)) k =
          monsterNortonLine01PairInverseOctadPositions a k := by
  apply monsterNortonOctadIndex_coordinate (monsterNortonLine01PairInverseOctadCodes a)
    (monsterNortonLine01PairInverseOctad_weight a) (monsterNortonLine01PairInverseOctadPositions a)
  · intro j
    have h := (positions_mem a (monsterNortonLine01PairInverseOctadPositions a j)).mpr
      (List.mem_ofFn.mpr ⟨j, rfl⟩)
    exact (Finset.mem_filter.mp h).2
  · intro j
    rw [positions_sort]
    exact position_index a j

/-- Every displayed pair uses the genuine increasing physical-coordinate representative. -/
theorem monsterNortonLine01PairInversePair_increasing (e : Fin 64) :
    monsterNortonLine01PairInversePairFirst e < monsterNortonLine01PairInversePairSecond e := by
  revert e
  decide +kernel

/-- The entire inverse-image label table in the original pair and octad short dictionary. -/
noncomputable def monsterNortonLine01PairInverseShortOutput (e : Fin 64) : GriessShortIndex :=
  if monsterNortonLine01PairInverseIsPair e then
    Sum.inl (monsterNortonLine01PairInversePairSign e,
      griessPairIndex (monsterNortonLine01PairInversePairFirst e)
        (monsterNortonLine01PairInversePairSecond e)
        (ne_of_lt (monsterNortonLine01PairInversePair_increasing e)))
  else
    Sum.inr (Sum.inl
      (monsterNortonOctadIndex
        (monsterNortonLine01PairInverseOctadCodes (monsterNortonLine01PairInverseOctadSlot e))
        (monsterNortonLine01PairInverseOctad_weight (monsterNortonLine01PairInverseOctadSlot e)),
          monsterNortonLine01PairInverseOctadSign e))

/-- Actual physical integer coordinates of all sixty-four inverse-image short vectors. -/
def monsterNortonLine01PairInverseShortIntegral (e : Fin 64) : Fin 24 → ℤ :=
  if monsterNortonLine01PairInverseIsPair e then
    fun i => 4 * (if i = monsterNortonLine01PairInversePairFirst e then 1 else 0) +
      (if monsterNortonLine01PairInversePairSign e = 0 then -4 else 4) *
        (if i = monsterNortonLine01PairInversePairSecond e then 1 else 0)
  else
    monsterNortonOctadIntegral
      (monsterNortonLine01PairInverseOctadCodes (monsterNortonLine01PairInverseOctadSlot e))
      (monsterNortonLine01PairInverseOctadPositions (monsterNortonLine01PairInverseOctadSlot e))
      (monsterNortonLine01PairInverseOctadSign e)

/-- The finite physical vectors are exactly their actual original dictionary values. -/
theorem monsterNortonLine01PairInverseShortIntegral_actual (e : Fin 64) :
    griessShortIntegral (monsterNortonLine01PairInverseShortOutput e) =
      monsterNortonLine01PairInverseShortIntegral e := by
  unfold monsterNortonLine01PairInverseShortOutput monsterNortonLine01PairInverseShortIntegral
  by_cases h : monsterNortonLine01PairInverseIsPair e = true
  · simp only [ite_eq_left h, griessShortIntegral, griessPairIndex_coordinates,
      monsterNortonLine01PairInversePair_increasing, ite_true]
  · simp only [ite_eq_right h]
    exact monsterNortonOctadIntegral_eq
      (monsterNortonLine01PairInverseOctadCodes (monsterNortonLine01PairInverseOctadSlot e))
      (monsterNortonLine01PairInverseOctad_weight (monsterNortonLine01PairInverseOctadSlot e))
      (monsterNortonLine01PairInverseOctadPositions (monsterNortonLine01PairInverseOctadSlot e))
      (monsterNortonLine01PairInverseOctad_coordinate (monsterNortonLine01PairInverseOctadSlot e))
      (monsterNortonLine01PairInverseOctadSign e)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

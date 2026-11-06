/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual source octad labels for the squared-U images of eight complementary pair units. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine02MiddleForwardPacket

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual source octad codes reached from the complementary plus-pair inputs. -/
def monsterNortonLine02MiddlePlusOctadCode : Fin 8 → Fin 4096 :=
  ![2396, 566, 2859, 1834, 810, 1590, 2615, 1089]

/-- Increasing physical supports of those eight genuine Golay octads. -/
def monsterNortonLine02MiddlePlusOctadPositions : Fin 8 → Fin 8 → Fin 24 :=
  ![
  ![0, 1, 4, 5, 8, 9, 12, 13],
  ![1, 3, 9, 10, 12, 13, 16, 18],
  ![0, 3, 8, 10, 12, 13, 20, 23],
  ![3, 4, 8, 9, 11, 13, 16, 23],
  ![1, 2, 9, 11, 12, 13, 20, 23],
  ![2, 4, 8, 9, 10, 13, 18, 20],
  ![0, 2, 8, 11, 12, 13, 16, 18],
  ![1, 2, 3, 5, 8, 13, 18, 23]]

/-- Original even-sign indices of the full complementary squared-U outputs. -/
def monsterNortonLine02MiddlePlusOctadSign : Fin 8 → Fin 64 :=
  ![51, 58, 58, 51, 58, 51, 58, 46]

/-- Every displayed code is a genuine weight-eight Golay codeword. -/
theorem monsterNortonLine02MiddlePlusOctad_weight (a : Fin 8) :
    golayMaskWeight (golayEncodedMask (monsterNortonLine02MiddlePlusOctadCode a).val) = 8 := by
  revert a
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check membership of the eight explicit source octad supports.
private theorem positions_mem (a : Fin 8) (i : Fin 24) :
    i ∈ golayMaskSupport (golayEncodedMask (monsterNortonLine02MiddlePlusOctadCode a).val) ↔
      i ∈ List.ofFn (monsterNortonLine02MiddlePlusOctadPositions a) := by
  revert a i
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check sortedness of the eight explicit source octad supports.
private theorem positions_sorted (a : Fin 8) :
    List.SortedLT (List.ofFn (monsterNortonLine02MiddlePlusOctadPositions a)) := by
  revert a
  decide +kernel

private theorem positions_sort (a : Fin 8) :
    (golayMaskSupport (golayEncodedMask (monsterNortonLine02MiddlePlusOctadCode a).val)).sort =
      List.ofFn (monsterNortonLine02MiddlePlusOctadPositions a) := by
  apply (golayMaskSupport _).sortedLT_sort.eq_of_mem_iff (positions_sorted a)
  intro i
  simp only [Finset.mem_sort]
  exact positions_mem a i

private theorem position_index (a : Fin 8) (k : Fin 8) :
    (List.ofFn (monsterNortonLine02MiddlePlusOctadPositions a)).idxOf
      (monsterNortonLine02MiddlePlusOctadPositions a k) = k.val := by
  revert a k
  decide +kernel

/-- These finite positions are the actual increasing octad coordinates. -/
theorem monsterNortonLine02MiddlePlusOctad_coordinate (a : Fin 8) (k : Fin 8) :
    golayOctadCoordinate
      (monsterNortonOctadIndex (monsterNortonLine02MiddlePlusOctadCode a)
        (monsterNortonLine02MiddlePlusOctad_weight a)) k =
          monsterNortonLine02MiddlePlusOctadPositions a k := by
  apply monsterNortonOctadIndex_coordinate (monsterNortonLine02MiddlePlusOctadCode a)
    (monsterNortonLine02MiddlePlusOctad_weight a) (monsterNortonLine02MiddlePlusOctadPositions a)
  · intro j
    have h := (positions_mem a (monsterNortonLine02MiddlePlusOctadPositions a j)).mpr
      (List.mem_ofFn.mpr ⟨j, rfl⟩)
    exact (Finset.mem_filter.mp h).2
  · intro j
    rw [positions_sort]
    exact position_index a j

/-- The whole actual complementary pair input at the original preferred physical pair. -/
noncomputable def monsterNortonLine02MiddlePlusInput (a : Fin 8) : GriessShortIndex :=
  Sum.inl (1, griessPairIndex 0
    (monsterNortonEvenShortPairSecond (Fin.natAdd 2 (Fin.castAdd 2 a)))
    (ne_of_lt (monsterNortonEvenShortPairSecond_positive _)))

/-- Its complete preferred physical integer vector. -/
def monsterNortonLine02MiddlePlusInputIntegral (a : Fin 8) : Fin 24 → ℤ := fun i =>
  4 * (if i = 0 then 1 else 0) +
    4 * (if i = monsterNortonEvenShortPairSecond (Fin.natAdd 2 (Fin.castAdd 2 a)) then 1 else 0)

/-- Every finite input formula is the exact original pair dictionary representative. -/
theorem monsterNortonLine02MiddlePlusInputIntegral_actual (a : Fin 8) :
    griessShortIntegral (monsterNortonLine02MiddlePlusInput a) =
      monsterNortonLine02MiddlePlusInputIntegral a := by
  simp only [monsterNortonLine02MiddlePlusInput, griessShortIntegral,
    griessPairIndex_coordinates, monsterNortonEvenShortPairSecond_positive, ite_true]
  rfl

/-- The actual source octad output, keeping its entire original even-sign label. -/
noncomputable def monsterNortonLine02MiddlePlusOutput (a : Fin 8) : GriessShortIndex :=
  Sum.inr (Sum.inl (monsterNortonOctadIndex (monsterNortonLine02MiddlePlusOctadCode a)
    (monsterNortonLine02MiddlePlusOctad_weight a), monsterNortonLine02MiddlePlusOctadSign a))

/-- Its finite complete physical representative. -/
def monsterNortonLine02MiddlePlusOutputIntegral (a : Fin 8) : Fin 24 → ℤ :=
  monsterNortonOctadIntegral (monsterNortonLine02MiddlePlusOctadCode a)
    (monsterNortonLine02MiddlePlusOctadPositions a) (monsterNortonLine02MiddlePlusOctadSign a)

/-- Every stored output formula is the exact original Conway octad representative. -/
theorem monsterNortonLine02MiddlePlusOutputIntegral_actual (a : Fin 8) :
    griessShortIntegral (monsterNortonLine02MiddlePlusOutput a) =
      monsterNortonLine02MiddlePlusOutputIntegral a :=
  monsterNortonOctadIntegral_eq _ _ _ (monsterNortonLine02MiddlePlusOctad_coordinate _) _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

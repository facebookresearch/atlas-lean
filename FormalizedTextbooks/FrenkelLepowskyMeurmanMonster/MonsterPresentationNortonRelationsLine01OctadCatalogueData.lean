/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A complete inverse catalogue for the actual reached octad short labels. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01OctadSixthCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The thirty-two actual octad sign labels occurring in every reached block. -/
def monsterNortonLine01OctadSignLabel : Fin 32 → Fin 64 := ![0, 3, 5, 6, 9, 10, 12, 15, 17, 18,
      20, 23, 24, 27, 29, 30, 33, 34, 36, 39, 40, 43, 45, 46, 48, 51, 53, 54, 57, 58, 60, 63]

/-- The direct inverse index on the thirty-two even sign labels. -/
def monsterNortonLine01OctadSignLookup (e : Fin 64) : Fin 32 := ⟨e.val / 2, by omega⟩

/-- Membership in the exact reached octad sign catalogue. -/
def monsterNortonLine01OctadSignSupport (e : Fin 64) : Prop :=
  monsterNortonLine01OctadSignLabel (monsterNortonLine01OctadSignLookup e) = e

instance (e : Fin 64) : Decidable (monsterNortonLine01OctadSignSupport e) :=
  inferInstanceAs (Decidable (_ = _))

/-- The original source-code index producing a reached octad coordinate. -/
def monsterNortonLine01OctadSourceA : Fin 16 → Fin 32 → Fin 64 :=
  ![![57, 60, 10, 18, 30, 6, 48, 53, 24, 0, 54, 51, 34, 39, 17, 9, 20, 12, 58, 63, 46, 43, 29,
      5, 40, 45, 27, 3, 15, 23, 33, 36],
    ![57, 30, 45, 23, 27, 33, 18, 53, 51, 9, 58, 29, 12, 43, 24, 34, 63, 5, 54, 17, 0, 39, 20,
      46, 40, 15, 60, 6, 10, 48, 3, 36],
    ![57, 53, 24, 9, 43, 58, 23, 27, 29, 12, 33, 45, 18, 30, 51, 34, 63, 46, 3, 15, 48, 60, 17,
      0, 6, 10, 39, 54, 20, 5, 40, 36],
    ![57, 53, 51, 34, 20, 5, 3, 15, 39, 54, 48, 60, 23, 27, 29, 12, 17, 0, 6, 10, 33, 45, 43,
      58, 18, 30, 24, 9, 63, 46, 40, 36],
    ![57, 6, 45, 15, 3, 33, 10, 53, 51, 17, 58, 5, 20, 43, 0, 34, 63, 29, 54, 9, 24, 39, 12, 46,
      40, 23, 60, 30, 18, 48, 27, 36],
    ![57, 53, 0, 17, 43, 58, 15, 3, 5, 20, 33, 45, 10, 6, 51, 34, 63, 46, 27, 23, 48, 60, 9, 24,
      30, 18, 39, 54, 12, 29, 40, 36],
    ![57, 53, 51, 34, 12, 29, 27, 23, 39, 54, 48, 60, 15, 3, 5, 20, 9, 24, 30, 18, 33, 45, 43,
      58, 10, 6, 0, 17, 63, 46, 40, 36],
    ![57, 48, 27, 15, 3, 23, 60, 53, 51, 39, 12, 5, 20, 29, 54, 34, 63, 43, 0, 9, 24, 17, 58,
      46, 40, 33, 10, 30, 18, 6, 45, 36],
    ![57, 53, 54, 39, 29, 12, 15, 3, 5, 20, 23, 27, 60, 48, 51, 34, 63, 46, 45, 33, 6, 10, 9,
      24, 30, 18, 17, 0, 58, 43, 40, 36],
    ![57, 53, 51, 34, 58, 43, 45, 33, 17, 0, 6, 10, 15, 3, 5, 20, 9, 24, 30, 18, 23, 27, 29, 12,
      60, 48, 54, 39, 63, 46, 40, 36],
    ![57, 53, 24, 9, 0, 17, 60, 48, 54, 39, 10, 6, 18, 30, 51, 34, 63, 46, 3, 15, 27, 23, 58,
      43, 45, 33, 12, 29, 20, 5, 40, 36],
    ![57, 53, 51, 34, 20, 5, 3, 15, 12, 29, 27, 23, 60, 48, 54, 39, 58, 43, 45, 33, 10, 6, 0,
      17, 18, 30, 24, 9, 63, 46, 40, 36],
    ![57, 30, 6, 60, 48, 10, 18, 53, 51, 9, 17, 54, 39, 0, 24, 34, 63, 5, 29, 58, 43, 12, 20,
      46, 40, 15, 23, 45, 33, 27, 3, 36],
    ![57, 23, 33, 18, 30, 45, 27, 53, 24, 43, 29, 51, 34, 12, 58, 9, 20, 39, 17, 63, 46, 0, 54,
      5, 40, 6, 48, 3, 15, 60, 10, 36],
    ![57, 15, 33, 10, 6, 45, 3, 53, 0, 43, 5, 51, 34, 20, 58, 17, 12, 39, 9, 63, 46, 24, 54, 29,
      40, 30, 48, 27, 23, 60, 18, 36],
    ![57, 15, 23, 60, 48, 27, 3, 53, 54, 29, 5, 51, 34, 20, 12, 39, 58, 17, 9, 63, 46, 24, 0,
      43, 40, 30, 6, 45, 33, 10, 18, 36]]

/-- The original physical-column slot producing a reached octad coordinate. -/
def monsterNortonLine01OctadSourceK : Fin 16 → Fin 32 → Fin 16 :=
  ![![11, 10, 7, 3, 5, 8, 14, 15, 4, 9, 12, 13, 1, 0, 2, 6, 6, 2, 0, 1, 13, 12, 9, 4, 15, 14, 8,
      5, 3, 7, 10, 11],
    ![5, 11, 7, 14, 10, 8, 15, 3, 6, 13, 9, 0, 12, 2, 1, 4, 4, 1, 2, 12, 0, 9, 13, 6, 3, 15, 8,
      10, 14, 7, 11, 5],
    ![4, 6, 11, 15, 7, 8, 12, 0, 10, 14, 9, 2, 13, 1, 3, 5, 5, 3, 1, 13, 2, 9, 14, 10, 0, 12, 8,
      7, 15, 11, 6, 4],
    ![6, 4, 5, 3, 11, 15, 13, 1, 7, 8, 9, 2, 0, 12, 14, 10, 10, 14, 12, 0, 2, 9, 8, 7, 1, 13,
      15, 11, 3, 5, 4, 6],
    ![8, 11, 3, 14, 10, 5, 15, 7, 2, 13, 4, 0, 12, 6, 1, 9, 9, 1, 6, 12, 0, 4, 13, 2, 7, 15, 5,
      10, 14, 3, 11, 8],
    ![9, 2, 11, 15, 3, 5, 12, 0, 10, 14, 4, 6, 13, 1, 7, 8, 8, 7, 1, 13, 6, 4, 14, 10, 0, 12, 5,
      3, 15, 11, 2, 9],
    ![2, 9, 8, 7, 11, 15, 13, 1, 3, 5, 4, 6, 0, 12, 14, 10, 10, 14, 12, 0, 6, 4, 5, 3, 1, 13,
      15, 11, 7, 8, 9, 2],
    ![14, 11, 3, 8, 7, 5, 15, 10, 0, 13, 4, 2, 9, 6, 1, 12, 12, 1, 6, 9, 2, 4, 13, 0, 10, 15, 5,
      7, 8, 3, 11, 14],
    ![12, 0, 11, 15, 3, 5, 9, 2, 7, 8, 4, 6, 13, 1, 10, 14, 14, 10, 1, 13, 6, 4, 8, 7, 2, 9, 5,
      3, 15, 11, 0, 12],
    ![0, 12, 14, 10, 11, 15, 13, 1, 3, 5, 4, 6, 2, 9, 8, 7, 7, 8, 9, 2, 6, 4, 5, 3, 1, 13, 15,
      11, 10, 14, 12, 0],
    ![13, 1, 3, 5, 7, 8, 12, 0, 10, 14, 9, 2, 4, 6, 11, 15, 15, 11, 6, 4, 2, 9, 14, 10, 0, 12,
      8, 7, 5, 3, 1, 13],
    ![1, 13, 15, 11, 3, 5, 4, 6, 7, 8, 9, 2, 0, 12, 14, 10, 10, 14, 12, 0, 2, 9, 8, 7, 6, 4, 5,
      3, 11, 15, 13, 1],
    ![15, 3, 7, 14, 10, 8, 5, 11, 1, 4, 9, 0, 12, 2, 6, 13, 13, 6, 2, 12, 0, 9, 4, 1, 11, 5, 8,
      10, 14, 7, 3, 15],
    ![3, 10, 7, 11, 15, 8, 14, 5, 13, 9, 12, 4, 6, 0, 2, 1, 1, 2, 0, 6, 4, 12, 9, 13, 5, 14, 8,
      15, 11, 7, 10, 3],
    ![7, 10, 3, 11, 15, 5, 14, 8, 13, 4, 12, 9, 2, 0, 6, 1, 1, 6, 0, 2, 9, 12, 4, 13, 8, 14, 5,
      15, 11, 3, 10, 7],
    ![10, 7, 3, 11, 15, 5, 8, 14, 13, 4, 9, 12, 0, 2, 6, 1, 1, 6, 2, 0, 12, 9, 4, 13, 14, 8, 5,
      15, 11, 3, 7, 10]]

set_option maxRecDepth 10000 in
/-- Every catalogue entry binds to its actual source family, octad block, and sign label. -/
theorem monsterNortonLine01OctadSource_right (j : Fin 16) (p : Fin 32) :
    monsterNortonLine01ShortInverseIsOctad (monsterNortonLine01OctadSourceA j p) = true ∧
      monsterNortonLine01ShortInverseOctadId (monsterNortonLine01OctadSourceA j p)
        (monsterNortonLine01OctadSourceK j p) = j ∧
      monsterNortonLine01ShortInverseOctadSigns (monsterNortonLine01OctadSourceA j p)
        (monsterNortonLine01OctadSourceK j p) = monsterNortonLine01OctadSignLabel p := by
  revert j p
  decide +kernel

set_option maxRecDepth 10000 in
/-- All actual source octad entries are recovered by the finite inverse catalogue. -/
theorem monsterNortonLine01OctadSource_left (a : Fin 64) (k : Fin 16)
    (h : monsterNortonLine01ShortInverseIsOctad a = true) :
    monsterNortonLine01OctadSignSupport (monsterNortonLine01ShortInverseOctadSigns a k) ∧
      monsterNortonLine01OctadSourceA (monsterNortonLine01ShortInverseOctadId a k)
        (monsterNortonLine01OctadSignLookup (monsterNortonLine01ShortInverseOctadSigns a k)) = a ∧
      monsterNortonLine01OctadSourceK (monsterNortonLine01ShortInverseOctadId a k)
        (monsterNortonLine01OctadSignLookup (monsterNortonLine01ShortInverseOctadSigns a k)) =
          k := by
  revert a k h
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

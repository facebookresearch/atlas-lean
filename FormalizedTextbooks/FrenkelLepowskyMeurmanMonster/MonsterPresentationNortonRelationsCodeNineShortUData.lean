/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Finite source-coordinate correspondence for the code-nine inverse short transport. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Original forward odd-code choices after inverse U. -/
def monsterNortonCodeNineShortUOutputCode : Fin 8 → Fin 32 → Fin 32 :=
  ![![4, 4, 2, 2, 4, 0, 2, 6,
    4, 0, 2, 6, 0, 0, 6, 6,
    3, 3, 1, 1, 3, 7, 1, 5,
    3, 7, 1, 5, 7, 7, 5, 5],
  ![1, 0, 6, 3, 1, 0, 6, 3,
    1, 0, 6, 3, 5, 4, 2, 7,
    7, 2, 4, 5, 7, 2, 4, 5,
    7, 2, 4, 5, 3, 6, 0, 1],
  ![10, 10, 11, 11, 13, 13, 8, 8,
    12, 12, 9, 9, 15, 15, 14, 14,
    10, 14, 11, 15, 13, 9, 8, 12,
    12, 8, 9, 13, 15, 11, 14, 10],
  ![20, 20, 18, 18, 21, 21, 23, 23,
    19, 19, 17, 17, 22, 22, 16, 16,
    20, 16, 18, 22, 21, 17, 23, 19,
    19, 23, 17, 21, 22, 18, 16, 20],
  ![14, 14, 15, 15, 9, 9, 12, 12,
    8, 8, 13, 13, 11, 11, 10, 10,
    14, 10, 15, 11, 9, 13, 12, 8,
    8, 12, 13, 9, 11, 15, 10, 14],
  ![16, 16, 22, 22, 17, 17, 19, 19,
    23, 23, 21, 21, 18, 18, 20, 20,
    16, 20, 22, 18, 17, 21, 19, 23,
    23, 19, 21, 17, 18, 22, 20, 16],
  ![25, 24, 30, 27, 25, 24, 30, 27,
    31, 26, 28, 29, 31, 26, 28, 29,
    25, 24, 30, 27, 29, 28, 26, 31,
    31, 26, 28, 29, 27, 30, 24, 25],
  ![29, 28, 26, 31, 29, 28, 26, 31,
    27, 30, 24, 25, 27, 30, 24, 25,
    29, 28, 26, 31, 25, 24, 30, 27,
    27, 30, 24, 25, 31, 26, 28, 29]]

/-- Original physical-column choices after inverse U. -/
def monsterNortonCodeNineShortUOutputColumn : Fin 8 → Fin 32 → Fin 8 :=
  ![![1, 0, 1, 0, 2, 3, 2, 3,
    3, 2, 3, 2, 0, 1, 0, 1,
    1, 0, 1, 0, 2, 3, 2, 3,
    3, 2, 3, 2, 0, 1, 0, 1],
  ![4, 4, 4, 4, 5, 5, 5, 5,
    7, 7, 7, 7, 6, 6, 6, 6,
    4, 4, 4, 4, 5, 5, 5, 5,
    7, 7, 7, 7, 6, 6, 6, 6],
  ![7, 4, 7, 4, 7, 4, 7, 4,
    7, 4, 7, 4, 7, 4, 7, 4,
    5, 6, 5, 6, 5, 6, 5, 6,
    5, 6, 5, 6, 5, 6, 5, 6],
  ![7, 4, 7, 4, 7, 4, 7, 4,
    7, 4, 7, 4, 7, 4, 7, 4,
    5, 6, 5, 6, 5, 6, 5, 6,
    5, 6, 5, 6, 5, 6, 5, 6],
  ![3, 0, 3, 0, 3, 0, 3, 0,
    3, 0, 3, 0, 3, 0, 3, 0,
    2, 1, 2, 1, 2, 1, 2, 1,
    2, 1, 2, 1, 2, 1, 2, 1],
  ![3, 0, 3, 0, 3, 0, 3, 0,
    3, 0, 3, 0, 3, 0, 3, 0,
    2, 1, 2, 1, 2, 1, 2, 1,
    2, 1, 2, 1, 2, 1, 2, 1],
  ![4, 4, 4, 4, 5, 5, 5, 5,
    4, 4, 4, 4, 5, 5, 5, 5,
    7, 7, 7, 7, 6, 6, 6, 6,
    7, 7, 7, 7, 6, 6, 6, 6],
  ![0, 0, 0, 0, 2, 2, 2, 2,
    0, 0, 0, 0, 2, 2, 2, 2,
    3, 3, 3, 3, 1, 1, 1, 1,
    3, 3, 3, 3, 1, 1, 1, 1]]

/-- The complete inverse-U central phases of the preferred source lifts. -/
def monsterNortonCodeNineShortUPhase : Fin 8 → Fin 32 → ZMod 2 :=
  ![![0, 1, 1, 0, 0, 0, 1, 1,
    0, 0, 1, 1, 1, 0, 0, 1,
    1, 0, 1, 0, 1, 1, 1, 1,
    1, 1, 1, 1, 0, 1, 0, 1],
  ![0, 1, 0, 0, 1, 0, 1, 1,
    1, 0, 1, 1, 1, 0, 1, 1,
    0, 0, 1, 0, 1, 1, 0, 1,
    1, 1, 0, 1, 1, 1, 0, 1],
  ![0, 1, 0, 1, 0, 1, 1, 0,
    1, 0, 0, 1, 0, 1, 0, 1,
    0, 0, 0, 0, 0, 0, 1, 1,
    1, 1, 0, 0, 0, 0, 0, 0],
  ![1, 0, 0, 1, 0, 1, 0, 1,
    0, 1, 0, 1, 0, 1, 1, 0,
    1, 1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 1, 1],
  ![0, 1, 0, 1, 0, 1, 1, 0,
    1, 0, 0, 1, 0, 1, 0, 1,
    0, 0, 0, 0, 0, 0, 1, 1,
    1, 1, 0, 0, 0, 0, 0, 0],
  ![1, 0, 0, 1, 0, 1, 0, 1,
    0, 1, 0, 1, 0, 1, 1, 0,
    1, 1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 1, 1],
  ![1, 0, 1, 1, 0, 1, 0, 0,
    1, 1, 0, 1, 0, 0, 1, 0,
    0, 1, 0, 0, 0, 1, 0, 0,
    0, 0, 1, 0, 0, 0, 1, 0],
  ![1, 0, 1, 1, 0, 1, 0, 0,
    1, 1, 0, 1, 0, 0, 1, 0,
    0, 1, 0, 0, 0, 1, 0, 0,
    0, 0, 1, 0, 0, 0, 1, 0]]

/-- The actual original forward coordinate selected for each inverse short entry. -/
def monsterNortonCodeNineShortUOutput (p : Fin 8 × Fin 32) : Fin 32 × Fin 8 :=
  (monsterNortonCodeNineShortUOutputCode p.1 p.2,
    monsterNortonCodeNineShortUOutputColumn p.1 p.2)

/-- All inverse short entries account for all forward short entries exactly once. -/
theorem monsterNortonCodeNineShortUOutput_bijective :
    Function.Bijective monsterNortonCodeNineShortUOutput := by
  decide +kernel

/-- The full inverse transport signs give the exact forward coefficients. -/
theorem monsterNortonCodeNineShortU_coefficient (p : Fin 8 × Fin 32) :
    monsterNortonCodeNineInverseShortCoefficient p.1 p.2 *
      nortonUIntegerSign (monsterNortonCodeNineShortUPhase p.1 p.2) =
        monsterNortonCodeNineForwardShortCoefficient
          (monsterNortonCodeNineShortUOutput p).1 (monsterNortonCodeNineShortUOutput p).2 := by
  revert p
  decide +kernel

/-- The complete preferred input Q evaluator uses the certified octad positions. -/
def monsterNortonCodeNineShortUInputQ (p : Fin 8 × Fin 32) : Q :=
  monsterNortonOctadQSource
    (monsterNortonRemainingOctadUCodes (monsterNortonCodeNineInverseOctadChoice p.1))
    (monsterNortonRemainingOctadUPositions (monsterNortonCodeNineInverseOctadChoice p.1))
    (monsterNortonCodeNineInverseSign p.1 p.2)

/-- This finite input evaluator is the actual original preferred source Q lift. -/
theorem monsterNortonCodeNineShortUInputQ_actual (p : Fin 8 × Fin 32) :
    monsterNortonShortQSource (monsterNortonCodeNineInverseShortIndex p) =
      monsterNortonCodeNineShortUInputQ p := by
  apply monsterNortonOctadQSource_actual
  exact monsterNortonRemainingOctadUPositions_actual _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

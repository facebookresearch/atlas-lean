/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Finite source-coordinate correspondence for the code-twenty-two inverse short transport. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyTwoMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Original forward odd-code choices after inverse U. -/
def monsterNortonCodeTwentyTwoShortUOutputCode : Fin 16 → Fin 32 → Fin 32 :=
  ![![18, 22, 3, 7, 5, 1, 16, 20,
    4, 0, 17, 21, 23, 19, 6, 2,
    26, 30, 15, 11, 9, 13, 24, 28,
    8, 12, 25, 29, 31, 27, 10, 14],
    ![10, 14, 4, 0, 26, 30, 16, 20,
    5, 1, 15, 11, 17, 21, 31, 27,
    3, 7, 9, 13, 23, 19, 25, 29,
    8, 12, 6, 2, 24, 28, 18, 22],
    ![19, 23, 2, 6, 5, 1, 16, 20,
    4, 0, 17, 21, 22, 18, 7, 3,
    27, 31, 14, 10, 9, 13, 24, 28,
    8, 12, 25, 29, 30, 26, 11, 15],
    ![11, 15, 4, 0, 27, 31, 16, 20,
    2, 6, 9, 13, 22, 18, 25, 29,
    5, 1, 14, 10, 17, 21, 30, 26,
    8, 12, 7, 3, 24, 28, 19, 23],
    ![13, 9, 4, 0, 29, 25, 16, 20,
    2, 6, 15, 11, 22, 18, 31, 27,
    3, 7, 14, 10, 23, 19, 30, 26,
    8, 12, 1, 5, 24, 28, 21, 17],
    ![21, 17, 2, 6, 3, 7, 16, 20,
    4, 0, 23, 19, 22, 18, 1, 5,
    29, 25, 14, 10, 15, 11, 24, 28,
    8, 12, 31, 27, 30, 26, 13, 9],
    ![0, 27, 4, 31, 15, 16, 11, 20,
    23, 8, 19, 12, 28, 7, 24, 3,
    5, 26, 1, 30, 14, 21, 10, 17,
    22, 13, 18, 9, 25, 6, 29, 2],
    ![30, 29, 26, 25, 23, 16, 19, 20,
    15, 8, 11, 12, 2, 1, 6, 5,
    3, 4, 7, 0, 14, 13, 10, 9,
    22, 21, 18, 17, 31, 24, 27, 28],
    ![31, 4, 27, 0, 15, 16, 11, 20,
    23, 8, 19, 12, 3, 24, 7, 28,
    2, 29, 6, 25, 22, 13, 18, 9,
    14, 21, 10, 17, 30, 1, 26, 5],
    ![25, 26, 29, 30, 23, 16, 19, 20,
    15, 8, 11, 12, 5, 6, 1, 2,
    28, 27, 24, 31, 22, 21, 18, 17,
    14, 13, 10, 9, 0, 7, 4, 3],
    ![12, 5, 29, 16, 8, 1, 25, 20,
    17, 28, 4, 13, 21, 24, 0, 9,
    15, 2, 26, 19, 11, 6, 30, 23,
    22, 31, 7, 10, 18, 27, 3, 14],
    ![20, 3, 27, 8, 16, 7, 31, 12,
    15, 28, 4, 19, 11, 24, 0, 23,
    17, 2, 26, 13, 21, 6, 30, 9,
    14, 25, 1, 18, 10, 29, 5, 22],
    ![24, 3, 28, 7, 15, 16, 11, 20,
    23, 8, 19, 12, 4, 31, 0, 27,
    29, 2, 25, 6, 14, 21, 10, 17,
    22, 13, 18, 9, 1, 30, 5, 26],
    ![6, 5, 2, 1, 23, 16, 19, 20,
    15, 8, 11, 12, 26, 25, 30, 29,
    27, 28, 31, 24, 14, 13, 10, 9,
    22, 21, 18, 17, 7, 0, 3, 4],
    ![7, 28, 3, 24, 15, 16, 11, 20,
    23, 8, 19, 12, 27, 0, 31, 4,
    26, 5, 30, 1, 22, 13, 18, 9,
    14, 21, 10, 17, 6, 25, 2, 29],
    ![1, 2, 5, 6, 23, 16, 19, 20,
    15, 8, 11, 12, 29, 30, 25, 26,
    4, 3, 0, 7, 22, 21, 18, 17,
    14, 13, 10, 9, 24, 31, 28, 27]]

/-- Original physical-column choices after inverse U. -/
def monsterNortonCodeTwentyTwoShortUOutputColumn : Fin 16 → Fin 32 → Fin 16 :=
  ![![15, 15, 5, 5, 9, 9, 3, 3,
    1, 1, 11, 11, 7, 7, 13, 13,
    14, 14, 4, 4, 8, 8, 2, 2,
    0, 0, 10, 10, 6, 6, 12, 12],
    ![15, 15, 2, 2, 13, 13, 0, 0,
    10, 10, 7, 7, 8, 8, 5, 5,
    6, 6, 11, 11, 4, 4, 9, 9,
    3, 3, 14, 14, 1, 1, 12, 12],
    ![15, 15, 5, 5, 1, 1, 11, 11,
    9, 9, 3, 3, 7, 7, 13, 13,
    14, 14, 4, 4, 0, 0, 10, 10,
    8, 8, 2, 2, 6, 6, 12, 12],
    ![15, 15, 10, 10, 13, 13, 8, 8,
    6, 6, 3, 3, 4, 4, 1, 1,
    2, 2, 7, 7, 0, 0, 5, 5,
    11, 11, 14, 14, 9, 9, 12, 12],
    ![15, 15, 6, 6, 13, 13, 4, 4,
    10, 10, 3, 3, 8, 8, 1, 1,
    2, 2, 11, 11, 0, 0, 9, 9,
    7, 7, 14, 14, 5, 5, 12, 12],
    ![15, 15, 9, 9, 1, 1, 7, 7,
    5, 5, 3, 3, 11, 11, 13, 13,
    14, 14, 8, 8, 0, 0, 6, 6,
    4, 4, 2, 2, 10, 10, 12, 12],
    ![15, 8, 15, 8, 10, 13, 10, 13,
    9, 14, 9, 14, 12, 11, 12, 11,
    7, 0, 7, 0, 2, 5, 2, 5,
    1, 6, 1, 6, 4, 3, 4, 3],
    ![15, 11, 15, 11, 6, 2, 6, 2,
    5, 1, 5, 1, 12, 8, 12, 8,
    4, 0, 4, 0, 13, 9, 13, 9,
    14, 10, 14, 10, 7, 3, 7, 3],
    ![15, 8, 15, 8, 13, 10, 13, 10,
    14, 9, 14, 9, 12, 11, 12, 11,
    4, 3, 4, 3, 6, 1, 6, 1,
    5, 2, 5, 2, 7, 0, 7, 0],
    ![15, 11, 15, 11, 2, 6, 2, 6,
    1, 5, 1, 5, 12, 8, 12, 8,
    7, 3, 7, 3, 10, 14, 10, 14,
    9, 13, 9, 13, 4, 0, 4, 0],
    ![15, 6, 5, 12, 15, 6, 5, 12,
    4, 13, 14, 7, 4, 13, 14, 7,
    11, 2, 1, 8, 11, 2, 1, 8,
    0, 9, 10, 3, 0, 9, 10, 3],
    ![15, 9, 10, 12, 15, 9, 10, 12,
    8, 14, 13, 11, 8, 14, 13, 11,
    7, 1, 2, 4, 7, 1, 2, 4,
    0, 6, 5, 3, 0, 6, 5, 3],
    ![15, 8, 15, 8, 9, 14, 9, 14,
    10, 13, 10, 13, 12, 11, 12, 11,
    7, 0, 7, 0, 1, 6, 1, 6,
    2, 5, 2, 5, 4, 3, 4, 3],
    ![15, 11, 15, 11, 5, 1, 5, 1,
    6, 2, 6, 2, 12, 8, 12, 8,
    4, 0, 4, 0, 14, 10, 14, 10,
    13, 9, 13, 9, 7, 3, 7, 3],
    ![15, 8, 15, 8, 14, 9, 14, 9,
    13, 10, 13, 10, 12, 11, 12, 11,
    4, 3, 4, 3, 5, 2, 5, 2,
    6, 1, 6, 1, 7, 0, 7, 0],
    ![15, 11, 15, 11, 1, 5, 1, 5,
    2, 6, 2, 6, 12, 8, 12, 8,
    7, 3, 7, 3, 9, 13, 9, 13,
    10, 14, 10, 14, 4, 0, 4, 0]]

/-- The complete inverse-U central phases of the preferred source lifts. -/
def monsterNortonCodeTwentyTwoShortUPhase : Fin 16 → Fin 32 → ZMod 2 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]]

/-- The actual original forward coordinate selected for each inverse short entry. -/
def monsterNortonCodeTwentyTwoShortUOutput (p : Fin 16 × Fin 32) : Fin 32 × Fin 16 :=
  (monsterNortonCodeTwentyTwoShortUOutputCode p.1 p.2,
    monsterNortonCodeTwentyTwoShortUOutputColumn p.1 p.2)

/-- All inverse short entries account for all forward short entries exactly once. -/
theorem monsterNortonCodeTwentyTwoShortUOutput_bijective :
    Function.Bijective monsterNortonCodeTwentyTwoShortUOutput := by
  decide +kernel

/-- The full inverse transport signs give the exact forward coefficients. -/
theorem monsterNortonCodeTwentyTwoShortU_coefficient (p : Fin 16 × Fin 32) :
    monsterNortonCodeTwentyTwoInverseShortCoefficient p.1 p.2 *
      nortonUIntegerSign (monsterNortonCodeTwentyTwoShortUPhase p.1 p.2) =
        monsterNortonCodeTwentyTwoForwardShortCoefficient
          (monsterNortonCodeTwentyTwoShortUOutput p).1 (monsterNortonCodeTwentyTwoShortUOutput
            p).2 := by
  revert p
  decide +kernel

/-- The complete preferred input Q evaluator uses the certified octad positions. -/
def monsterNortonCodeTwentyTwoShortUInputQ (p : Fin 16 × Fin 32) : Q :=
  monsterNortonOctadQSource
    (monsterNortonRemainingOctadUCodes (monsterNortonCodeTwentyTwoInverseOctadChoice p.1))
    (monsterNortonRemainingOctadUPositions (monsterNortonCodeTwentyTwoInverseOctadChoice p.1))
    (monsterNortonCodeTwentyTwoInverseSign p.1 p.2)

/-- This finite input evaluator is the actual original preferred source Q lift. -/
theorem monsterNortonCodeTwentyTwoShortUInputQ_actual (p : Fin 16 × Fin 32) :
    monsterNortonShortQSource (monsterNortonCodeTwentyTwoInverseShortIndex p) =
      monsterNortonCodeTwentyTwoShortUInputQ p := by
  apply monsterNortonOctadQSource_actual
  exact monsterNortonRemainingOctadUPositions_actual _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

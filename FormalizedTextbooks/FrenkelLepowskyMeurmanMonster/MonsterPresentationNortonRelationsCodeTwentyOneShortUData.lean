/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact preferred-octad correspondence of inverse U on the code-twentyone short candidates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyOneMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Complete actual inverse-U OutputOctad entries of the preferred-lift correspondence. -/
def monsterNortonCodeTwentyOneShortUOutputOctad : Fin 8 → Fin 32 → Fin 8 :=
  ![![5, 2, 1, 7, 4, 0, 3, 6,
    4, 0, 3, 6, 4, 0, 3, 6,
    7, 1, 2, 5, 6, 3, 0, 4,
    6, 3, 0, 4, 6, 3, 0, 4],
  ![5, 1, 2, 7, 4, 3, 0, 6,
    7, 2, 1, 5, 6, 0, 3, 4,
    4, 3, 0, 6, 4, 3, 0, 6,
    6, 0, 3, 4, 6, 0, 3, 4],
  ![4, 5, 5, 5, 6, 7, 7, 7,
    5, 5, 5, 4, 7, 7, 7, 6,
    3, 1, 1, 1, 0, 2, 2, 2,
    1, 1, 1, 3, 2, 2, 2, 0],
  ![4, 5, 3, 1, 0, 2, 6, 7,
    6, 7, 0, 2, 3, 1, 4, 5,
    5, 5, 1, 1, 2, 2, 7, 7,
    7, 7, 2, 2, 1, 1, 5, 5],
  ![4, 5, 5, 5, 0, 2, 2, 2,
    3, 1, 1, 1, 6, 7, 7, 7,
    6, 7, 7, 7, 3, 1, 1, 1,
    0, 2, 2, 2, 4, 5, 5, 5],
  ![5, 2, 1, 7, 7, 1, 2, 5,
    4, 0, 3, 6, 6, 3, 0, 4,
    4, 0, 3, 6, 6, 3, 0, 4,
    4, 0, 3, 6, 6, 3, 0, 4],
  ![5, 1, 2, 7, 7, 2, 1, 5,
    4, 3, 0, 6, 6, 0, 3, 4,
    4, 3, 0, 6, 6, 0, 3, 4,
    4, 3, 0, 6, 6, 0, 3, 4],
  ![4, 5, 5, 5, 3, 1, 1, 1,
    0, 2, 2, 2, 6, 7, 7, 7,
    6, 7, 7, 7, 0, 2, 2, 2,
    3, 1, 1, 1, 4, 5, 5, 5]]

/-- Complete actual inverse-U OutputSign entries of the preferred-lift correspondence. -/
def monsterNortonCodeTwentyOneShortUOutputSign : Fin 8 → Fin 32 → Fin 32 :=
  ![![15, 9, 11, 13, 8, 14, 12, 10,
    16, 22, 20, 18, 24, 30, 28, 26,
    10, 12, 14, 8, 13, 11, 9, 15,
    21, 19, 17, 23, 29, 27, 25, 31],
  ![13, 14, 11, 8, 10, 9, 12, 15,
    15, 12, 9, 10, 8, 11, 14, 13,
    18, 17, 20, 23, 26, 25, 28, 31,
    16, 19, 22, 21, 24, 27, 30, 29],
  ![7, 24, 16, 0, 5, 26, 18, 2,
    7, 23, 31, 0, 5, 21, 29, 2,
    4, 27, 19, 3, 6, 25, 17, 1,
    4, 20, 28, 3, 6, 22, 30, 1],
  ![5, 2, 6, 1, 3, 4, 0, 7,
    7, 0, 4, 3, 1, 6, 2, 5,
    21, 29, 22, 30, 19, 27, 16, 24,
    23, 31, 20, 28, 17, 25, 18, 26],
  ![6, 22, 30, 1, 7, 23, 31, 0,
    5, 21, 29, 2, 4, 20, 28, 3,
    3, 19, 27, 4, 2, 18, 26, 5,
    0, 16, 24, 7, 1, 17, 25, 6],
  ![14, 15, 13, 12, 11, 10, 8, 9,
    17, 16, 18, 19, 20, 21, 23, 22,
    25, 24, 26, 27, 28, 29, 31, 30,
    9, 8, 10, 11, 12, 13, 15, 14],
  ![12, 8, 13, 9, 14, 10, 15, 11,
    19, 23, 18, 22, 17, 21, 16, 20,
    27, 31, 26, 30, 25, 29, 24, 28,
    11, 15, 10, 14, 9, 13, 8, 12],
  ![4, 20, 28, 3, 0, 16, 24, 7,
    5, 21, 29, 2, 1, 17, 25, 6,
    6, 22, 30, 1, 2, 18, 26, 5,
    7, 23, 31, 0, 3, 19, 27, 4]]

/-- Complete actual inverse-U Phase entries of the preferred-lift correspondence. -/
def monsterNortonCodeTwentyOneShortUPhase : Fin 8 → Fin 32 → ZMod 2 :=
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
    0, 0, 0, 0, 0, 0, 0, 0]]

/-- The complete genuine forward octad-sign coordinate chosen for each inverse entry. -/
def monsterNortonCodeTwentyOneShortUOutput (p : Fin 8 × Fin 32) : Fin 8 × Fin 32 :=
  (monsterNortonCodeTwentyOneShortUOutputOctad p.1 p.2,
    monsterNortonCodeTwentyOneShortUOutputSign p.1 p.2)

/-- Every original forward short coordinate occurs exactly once. -/
theorem monsterNortonCodeTwentyOneShortUOutput_bijective :
    Function.Bijective monsterNortonCodeTwentyOneShortUOutput := by
  decide +kernel

/-- Full central phases preserve the exact normalized candidate coefficients. -/
theorem monsterNortonCodeTwentyOneShortU_coefficient (p : Fin 8 × Fin 32) :
    monsterNortonCodeTwentyOneInverseShortCoefficient p.1 p.2 *
      nortonUIntegerSign (monsterNortonCodeTwentyOneShortUPhase p.1 p.2) =
        monsterNortonCodeTwentyOneForwardShortCoefficient
          (monsterNortonCodeTwentyOneShortUOutput p).1
            (monsterNortonCodeTwentyOneShortUOutput p).2 := by
  revert p
  decide +kernel

/-- The full finite input Q evaluator at its certified physical octad coordinates. -/
def monsterNortonCodeTwentyOneShortUInputQ (p : Fin 8 × Fin 32) : Q :=
  monsterNortonOctadQSource
    (monsterNortonRemainingOctadUCodes (monsterNortonCodeTwentyOneInverseOctadChoice p.1))
    (monsterNortonRemainingOctadUPositions (monsterNortonCodeTwentyOneInverseOctadChoice p.1))
    (monsterNortonCodeTwentyOneInverseSign p.1 p.2)

/-- The finite input is exactly its original preferred source Q lift. -/
theorem monsterNortonCodeTwentyOneShortUInputQ_actual (p : Fin 8 × Fin 32) :
    monsterNortonShortQSource (monsterNortonCodeTwentyOneInverseShortIndex p) =
      monsterNortonCodeTwentyOneShortUInputQ p := by
  apply monsterNortonOctadQSource_actual
  exact monsterNortonRemainingOctadUPositions_actual _

/-- The full finite forward Q evaluator uses the actual increasing physical octad coordinates. -/
def monsterNortonCodeTwentyOneForwardShortQ (p : Fin 8 × Fin 32) : Q :=
  let a := monsterNortonCodeTwentyOneForwardOctadChoice p.1
  monsterNortonOctadQSource (monsterNortonEvenShortInverseUOctadCodes a)
    (monsterNortonEvenShortInverseUOctadPositions a) (monsterNortonCodeTwentyOneForwardSign p.1 p.2)

/-- The finite forward Q evaluator is the complete original preferred lift. -/
theorem monsterNortonCodeTwentyOneForwardShortQ_actual (p : Fin 8 × Fin 32) :
    monsterNortonShortQSource (monsterNortonCodeTwentyOneForwardShortIndex p) =
      monsterNortonCodeTwentyOneForwardShortQ p := by
  apply monsterNortonOctadQSource_actual
  exact monsterNortonEvenShortInverseUOctad_coordinate _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

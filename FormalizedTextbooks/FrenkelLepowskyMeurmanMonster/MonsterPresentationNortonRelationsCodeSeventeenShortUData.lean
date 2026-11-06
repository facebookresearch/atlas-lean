/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact preferred-octad correspondence of inverse U on the code-seventeen short candidates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSeventeenMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Complete actual inverse-U OutputOctad entries of the preferred-lift correspondence. -/
def monsterNortonCodeSeventeenShortUOutputOctad : Fin 8 → Fin 32 → Fin 8 :=
  ![![2, 3, 5, 6, 0, 1, 4, 7,
    0, 1, 4, 7, 0, 1, 4, 7,
    0, 1, 4, 7, 0, 1, 4, 7,
    0, 1, 4, 7, 2, 3, 5, 6],
  ![2, 6, 5, 3, 3, 5, 6, 2,
    0, 7, 4, 1, 1, 4, 7, 0,
    0, 7, 4, 1, 1, 4, 7, 0,
    0, 7, 4, 1, 1, 4, 7, 0],
  ![0, 2, 7, 6, 4, 5, 1, 3,
    1, 3, 4, 5, 7, 6, 0, 2,
    2, 2, 6, 6, 5, 5, 3, 3,
    3, 3, 5, 5, 6, 6, 2, 2],
  ![0, 2, 7, 6, 4, 5, 1, 3,
    1, 3, 4, 5, 7, 6, 0, 2,
    2, 2, 6, 6, 5, 5, 3, 3,
    3, 3, 5, 5, 6, 6, 2, 2],
  ![0, 1, 2, 3, 7, 4, 6, 5,
    4, 7, 5, 6, 1, 0, 3, 2,
    2, 3, 2, 3, 6, 5, 6, 5,
    5, 6, 5, 6, 3, 2, 3, 2],
  ![2, 3, 6, 5, 5, 6, 3, 2,
    0, 1, 7, 4, 4, 7, 1, 0,
    0, 1, 7, 4, 4, 7, 1, 0,
    0, 1, 7, 4, 4, 7, 1, 0],
  ![2, 6, 5, 3, 0, 7, 4, 1,
    3, 5, 6, 2, 1, 4, 7, 0,
    0, 7, 4, 1, 0, 7, 4, 1,
    1, 4, 7, 0, 1, 4, 7, 0],
  ![0, 1, 2, 3, 4, 7, 5, 6,
    7, 4, 6, 5, 1, 0, 3, 2,
    2, 3, 2, 3, 5, 6, 5, 6,
    6, 5, 6, 5, 3, 2, 3, 2]]

/-- Complete actual inverse-U OutputSign entries of the preferred-lift correspondence. -/
def monsterNortonCodeSeventeenShortUOutputSign : Fin 8 → Fin 32 → Fin 32 :=
  ![![15, 13, 9, 11, 8, 10, 14, 12,
    23, 21, 17, 19, 31, 29, 25, 27,
    24, 26, 30, 28, 16, 18, 22, 20,
    15, 13, 9, 11, 8, 10, 14, 12],
  ![13, 9, 12, 8, 15, 11, 14, 10,
    29, 25, 28, 24, 31, 27, 30, 26,
    18, 22, 19, 23, 16, 20, 17, 21,
    13, 9, 12, 8, 15, 11, 14, 10],
  ![7, 0, 4, 3, 6, 1, 5, 2,
    2, 5, 1, 6, 3, 4, 0, 7,
    24, 16, 27, 19, 25, 17, 26, 18,
    29, 21, 30, 22, 28, 20, 31, 23],
  ![5, 2, 1, 6, 4, 3, 0, 7,
    7, 0, 3, 4, 6, 1, 2, 5,
    26, 18, 30, 22, 27, 19, 31, 23,
    24, 16, 28, 20, 25, 17, 29, 21],
  ![6, 3, 1, 4, 2, 7, 5, 0,
    0, 5, 7, 2, 4, 1, 3, 6,
    25, 28, 17, 20, 29, 24, 21, 16,
    31, 26, 23, 18, 27, 30, 19, 22],
  ![14, 11, 10, 15, 8, 13, 12, 9,
    30, 27, 26, 31, 24, 29, 28, 25,
    17, 20, 21, 16, 23, 18, 19, 22,
    14, 11, 10, 15, 8, 13, 12, 9],
  ![12, 8, 13, 9, 19, 23, 18, 22,
    14, 10, 15, 11, 17, 21, 16, 20,
    12, 8, 13, 9, 28, 24, 29, 25,
    14, 10, 15, 11, 30, 26, 31, 27],
  ![4, 6, 3, 1, 2, 0, 5, 7,
    7, 5, 0, 2, 1, 3, 6, 4,
    27, 25, 19, 17, 29, 31, 21, 23,
    24, 26, 16, 18, 30, 28, 22, 20]]

/-- Complete actual inverse-U Phase entries of the preferred-lift correspondence. -/
def monsterNortonCodeSeventeenShortUPhase : Fin 8 → Fin 32 → ZMod 2 :=
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
def monsterNortonCodeSeventeenShortUOutput (p : Fin 8 × Fin 32) : Fin 8 × Fin 32 :=
  (monsterNortonCodeSeventeenShortUOutputOctad p.1 p.2,
    monsterNortonCodeSeventeenShortUOutputSign p.1 p.2)

/-- Every original forward short coordinate occurs exactly once. -/
theorem monsterNortonCodeSeventeenShortUOutput_bijective :
    Function.Bijective monsterNortonCodeSeventeenShortUOutput := by
  decide +kernel

/-- Full central phases preserve the exact normalized candidate coefficients. -/
theorem monsterNortonCodeSeventeenShortU_coefficient (p : Fin 8 × Fin 32) :
    monsterNortonCodeSeventeenInverseShortCoefficient p.1 p.2 *
      nortonUIntegerSign (monsterNortonCodeSeventeenShortUPhase p.1 p.2) =
        monsterNortonCodeSeventeenForwardShortCoefficient
          (monsterNortonCodeSeventeenShortUOutput p).1
            (monsterNortonCodeSeventeenShortUOutput p).2 := by
  revert p
  decide +kernel

/-- The full finite input Q evaluator at its certified physical octad coordinates. -/
def monsterNortonCodeSeventeenShortUInputQ (p : Fin 8 × Fin 32) : Q :=
  monsterNortonOctadQSource
    (monsterNortonRemainingOctadUCodes (monsterNortonCodeSeventeenInverseOctadChoice p.1))
    (monsterNortonRemainingOctadUPositions (monsterNortonCodeSeventeenInverseOctadChoice p.1))
    (monsterNortonCodeSeventeenInverseSign p.1 p.2)

/-- The finite input is exactly its original preferred source Q lift. -/
theorem monsterNortonCodeSeventeenShortUInputQ_actual (p : Fin 8 × Fin 32) :
    monsterNortonShortQSource (monsterNortonCodeSeventeenInverseShortIndex p) =
      monsterNortonCodeSeventeenShortUInputQ p := by
  apply monsterNortonOctadQSource_actual
  exact monsterNortonRemainingOctadUPositions_actual _

/-- The full finite forward Q evaluator uses the actual increasing physical octad coordinates. -/
def monsterNortonCodeSeventeenForwardShortQ (p : Fin 8 × Fin 32) : Q :=
  let a := monsterNortonCodeSeventeenForwardOctadChoice p.1
  monsterNortonOctadQSource (monsterNortonEvenShortInverseUOctadCodes a)
    (monsterNortonEvenShortInverseUOctadPositions a) (monsterNortonCodeSeventeenForwardSign p.1 p.2)

/-- The finite forward Q evaluator is the complete original preferred lift. -/
theorem monsterNortonCodeSeventeenForwardShortQ_actual (p : Fin 8 × Fin 32) :
    monsterNortonShortQSource (monsterNortonCodeSeventeenForwardShortIndex p) =
      monsterNortonCodeSeventeenForwardShortQ p := by
  apply monsterNortonOctadQSource_actual
  exact monsterNortonEvenShortInverseUOctad_coordinate _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

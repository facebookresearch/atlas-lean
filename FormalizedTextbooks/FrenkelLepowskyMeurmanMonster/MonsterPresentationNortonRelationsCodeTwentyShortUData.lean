/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact preferred-octad correspondence of inverse U on the code-twenty short candidates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Complete actual inverse-U OutputOctad entries of the preferred-lift correspondence. -/
def monsterNortonCodeTwentyShortUOutputOctad : Fin 8 → Fin 32 → Fin 8 :=
  ![![5, 2, 1, 7, 4, 0, 3, 6,
    7, 1, 2, 5, 6, 3, 0, 4,
    4, 0, 3, 6, 4, 0, 3, 6,
    6, 3, 0, 4, 6, 3, 0, 4],
  ![5, 7, 4, 6, 4, 6, 4, 6,
    4, 6, 4, 6, 4, 6, 5, 7,
    2, 1, 0, 3, 0, 3, 0, 3,
    0, 3, 0, 3, 0, 3, 2, 1],
  ![4, 5, 0, 2, 3, 1, 6, 7,
    6, 7, 3, 1, 0, 2, 4, 5,
    5, 5, 2, 2, 1, 1, 7, 7,
    7, 7, 1, 1, 2, 2, 5, 5],
  ![4, 5, 3, 1, 0, 2, 6, 7,
    5, 5, 1, 1, 2, 2, 7, 7,
    6, 7, 0, 2, 3, 1, 4, 5,
    7, 7, 2, 2, 1, 1, 5, 5],
  ![4, 5, 5, 5, 3, 1, 1, 1,
    0, 2, 2, 2, 6, 7, 7, 7,
    6, 7, 7, 7, 0, 2, 2, 2,
    3, 1, 1, 1, 4, 5, 5, 5],
  ![5, 1, 2, 7, 7, 2, 1, 5,
    4, 3, 0, 6, 6, 0, 3, 4,
    4, 3, 0, 6, 6, 0, 3, 4,
    4, 3, 0, 6, 6, 0, 3, 4],
  ![5, 2, 1, 7, 7, 1, 2, 5,
    4, 0, 3, 6, 6, 3, 0, 4,
    4, 0, 3, 6, 6, 3, 0, 4,
    4, 0, 3, 6, 6, 3, 0, 4],
  ![4, 5, 5, 5, 0, 2, 2, 2,
    3, 1, 1, 1, 6, 7, 7, 7,
    6, 7, 7, 7, 3, 1, 1, 1,
    0, 2, 2, 2, 4, 5, 5, 5]]

/-- Complete actual inverse-U OutputSign entries of the preferred-lift correspondence. -/
def monsterNortonCodeTwentyShortUOutputSign : Fin 8 → Fin 32 → Fin 32 :=
  ![![13, 11, 14, 8, 18, 20, 17, 23,
    15, 9, 12, 10, 16, 22, 19, 21,
    29, 27, 30, 24, 13, 11, 14, 8,
    31, 25, 28, 26, 15, 9, 12, 10],
  ![15, 13, 8, 10, 24, 26, 16, 18,
    23, 21, 31, 29, 15, 13, 8, 10,
    14, 12, 9, 11, 25, 27, 17, 19,
    22, 20, 30, 28, 14, 12, 9, 11],
  ![5, 2, 3, 4, 6, 1, 0, 7,
    7, 0, 1, 6, 4, 3, 2, 5,
    26, 18, 28, 20, 25, 17, 31, 23,
    24, 16, 30, 22, 27, 19, 29, 21],
  ![7, 0, 3, 4, 1, 6, 5, 2,
    24, 16, 28, 20, 30, 22, 26, 18,
    2, 5, 6, 1, 4, 3, 0, 7,
    29, 21, 25, 17, 27, 19, 31, 23],
  ![6, 25, 17, 1, 5, 26, 18, 2,
    7, 24, 16, 0, 4, 27, 19, 3,
    3, 28, 20, 4, 0, 31, 23, 7,
    2, 29, 21, 5, 1, 30, 22, 6],
  ![14, 13, 15, 12, 11, 8, 10, 9,
    30, 29, 31, 28, 27, 24, 26, 25,
    14, 13, 15, 12, 11, 8, 10, 9,
    17, 18, 16, 19, 20, 23, 21, 22],
  ![12, 13, 8, 9, 14, 15, 10, 11,
    28, 29, 24, 25, 30, 31, 26, 27,
    12, 13, 8, 9, 14, 15, 10, 11,
    19, 18, 23, 22, 17, 16, 21, 20],
  ![4, 27, 19, 3, 5, 26, 18, 2,
    0, 31, 23, 7, 1, 30, 22, 6,
    6, 25, 17, 1, 7, 24, 16, 0,
    2, 29, 21, 5, 3, 28, 20, 4]]

/-- Complete actual inverse-U Phase entries of the preferred-lift correspondence. -/
def monsterNortonCodeTwentyShortUPhase : Fin 8 → Fin 32 → ZMod 2 :=
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
def monsterNortonCodeTwentyShortUOutput (p : Fin 8 × Fin 32) : Fin 8 × Fin 32 :=
  (monsterNortonCodeTwentyShortUOutputOctad p.1 p.2,
    monsterNortonCodeTwentyShortUOutputSign p.1 p.2)

/-- Every original forward short coordinate occurs exactly once. -/
theorem monsterNortonCodeTwentyShortUOutput_bijective :
    Function.Bijective monsterNortonCodeTwentyShortUOutput := by
  decide +kernel

/-- Full central phases preserve the exact normalized candidate coefficients. -/
theorem monsterNortonCodeTwentyShortU_coefficient (p : Fin 8 × Fin 32) :
    monsterNortonCodeTwentyInverseShortCoefficient p.1 p.2 *
      nortonUIntegerSign (monsterNortonCodeTwentyShortUPhase p.1 p.2) =
        monsterNortonCodeTwentyForwardShortCoefficient
          (monsterNortonCodeTwentyShortUOutput p).1 (monsterNortonCodeTwentyShortUOutput p).2 := by
  revert p
  decide +kernel

/-- The full finite input Q evaluator at its certified physical octad coordinates. -/
def monsterNortonCodeTwentyShortUInputQ (p : Fin 8 × Fin 32) : Q :=
  monsterNortonOctadQSource
    (monsterNortonRemainingOctadUCodes (monsterNortonCodeTwentyInverseOctadChoice p.1))
    (monsterNortonRemainingOctadUPositions (monsterNortonCodeTwentyInverseOctadChoice p.1))
    (monsterNortonCodeTwentyInverseSign p.1 p.2)

/-- The finite input is exactly its original preferred source Q lift. -/
theorem monsterNortonCodeTwentyShortUInputQ_actual (p : Fin 8 × Fin 32) :
    monsterNortonShortQSource (monsterNortonCodeTwentyInverseShortIndex p) =
      monsterNortonCodeTwentyShortUInputQ p := by
  apply monsterNortonOctadQSource_actual
  exact monsterNortonRemainingOctadUPositions_actual _

/-- The full finite forward Q evaluator uses the actual increasing physical octad coordinates. -/
def monsterNortonCodeTwentyForwardShortQ (p : Fin 8 × Fin 32) : Q :=
  let a := monsterNortonCodeTwentyForwardOctadChoice p.1
  monsterNortonOctadQSource (monsterNortonEvenShortInverseUOctadCodes a)
    (monsterNortonEvenShortInverseUOctadPositions a) (monsterNortonCodeTwentyForwardSign p.1 p.2)

/-- The finite forward Q evaluator is the complete original preferred lift. -/
theorem monsterNortonCodeTwentyForwardShortQ_actual (p : Fin 8 × Fin 32) :
    monsterNortonShortQSource (monsterNortonCodeTwentyForwardShortIndex p) =
      monsterNortonCodeTwentyForwardShortQ p := by
  apply monsterNortonOctadQSource_actual
  exact monsterNortonEvenShortInverseUOctad_coordinate _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact preferred-octad correspondence of inverse U on the code-nineteen short candidates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineteenMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Complete actual inverse-U OutputOctad entries of the preferred-lift correspondence. -/
def monsterNortonCodeNineteenShortUOutputOctad : Fin 8 → Fin 32 → Fin 8 :=
  ![![2, 1, 5, 7, 0, 3, 4, 6,
    0, 3, 4, 6, 0, 3, 4, 6,
    7, 5, 1, 2, 6, 4, 3, 0,
    6, 4, 3, 0, 6, 4, 3, 0],
  ![2, 1, 5, 7, 0, 3, 4, 6,
    7, 5, 1, 2, 6, 4, 3, 0,
    0, 3, 4, 6, 0, 3, 4, 6,
    6, 4, 3, 0, 6, 4, 3, 0],
  ![0, 2, 2, 2, 3, 1, 1, 1,
    4, 5, 5, 5, 6, 7, 7, 7,
    2, 2, 2, 0, 1, 1, 1, 3,
    5, 5, 5, 4, 7, 7, 7, 6],
  ![0, 2, 6, 7, 4, 5, 3, 1,
    3, 1, 4, 5, 6, 7, 0, 2,
    2, 2, 7, 7, 5, 5, 1, 1,
    1, 1, 5, 5, 7, 7, 2, 2],
  ![0, 2, 2, 2, 4, 5, 5, 5,
    6, 7, 7, 7, 3, 1, 1, 1,
    2, 2, 2, 0, 5, 5, 5, 4,
    7, 7, 7, 6, 1, 1, 1, 3],
  ![2, 1, 7, 5, 5, 7, 1, 2,
    0, 3, 6, 4, 4, 6, 3, 0,
    0, 3, 6, 4, 4, 6, 3, 0,
    0, 3, 6, 4, 4, 6, 3, 0],
  ![2, 7, 5, 1, 0, 6, 4, 3,
    0, 6, 4, 3, 0, 6, 4, 3,
    1, 5, 7, 2, 3, 4, 6, 0,
    3, 4, 6, 0, 3, 4, 6, 0],
  ![0, 2, 2, 2, 6, 7, 7, 7,
    4, 5, 5, 5, 3, 1, 1, 1,
    2, 2, 2, 0, 7, 7, 7, 6,
    5, 5, 5, 4, 1, 1, 1, 3]]

/-- Complete actual inverse-U OutputSign entries of the preferred-lift correspondence. -/
def monsterNortonCodeNineteenShortUOutputSign : Fin 8 → Fin 32 → Fin 32 :=
  ![![15, 13, 9, 11, 24, 26, 30, 28,
    23, 21, 17, 19, 15, 13, 9, 11,
    12, 14, 10, 8, 27, 25, 29, 31,
    20, 22, 18, 16, 12, 14, 10, 8],
  ![13, 8, 11, 14, 26, 31, 28, 25,
    9, 12, 15, 10, 30, 27, 24, 29,
    21, 16, 19, 22, 13, 8, 11, 14,
    17, 20, 23, 18, 9, 12, 15, 10],
  ![7, 24, 16, 0, 5, 26, 18, 2,
    1, 30, 22, 6, 3, 28, 20, 4,
    7, 23, 31, 0, 5, 21, 29, 2,
    1, 17, 25, 6, 3, 19, 27, 4],
  ![5, 2, 1, 6, 4, 3, 0, 7,
    7, 0, 3, 4, 6, 1, 2, 5,
    21, 29, 17, 25, 20, 28, 16, 24,
    23, 31, 19, 27, 22, 30, 18, 26],
  ![6, 25, 17, 1, 7, 24, 16, 0,
    5, 26, 18, 2, 4, 27, 19, 3,
    6, 22, 30, 1, 7, 23, 31, 0,
    5, 21, 29, 2, 4, 20, 28, 3],
  ![14, 11, 10, 15, 8, 13, 12, 9,
    14, 11, 10, 15, 8, 13, 12, 9,
    25, 28, 29, 24, 31, 26, 27, 30,
    22, 19, 18, 23, 16, 21, 20, 17],
  ![12, 8, 13, 9, 27, 31, 26, 30,
    20, 16, 21, 17, 12, 8, 13, 9,
    14, 10, 15, 11, 25, 29, 24, 28,
    22, 18, 23, 19, 14, 10, 15, 11],
  ![4, 27, 19, 3, 0, 31, 23, 7,
    5, 26, 18, 2, 1, 30, 22, 6,
    4, 20, 28, 3, 0, 16, 24, 7,
    5, 21, 29, 2, 1, 17, 25, 6]]

/-- Complete actual inverse-U Phase entries of the preferred-lift correspondence. -/
def monsterNortonCodeNineteenShortUPhase : Fin 8 → Fin 32 → ZMod 2 :=
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
def monsterNortonCodeNineteenShortUOutput (p : Fin 8 × Fin 32) : Fin 8 × Fin 32 :=
  (monsterNortonCodeNineteenShortUOutputOctad p.1 p.2,
    monsterNortonCodeNineteenShortUOutputSign p.1 p.2)

/-- Every original forward short coordinate occurs exactly once. -/
theorem monsterNortonCodeNineteenShortUOutput_bijective :
    Function.Bijective monsterNortonCodeNineteenShortUOutput := by
  decide +kernel

/-- Full central phases preserve the exact normalized candidate coefficients. -/
theorem monsterNortonCodeNineteenShortU_coefficient (p : Fin 8 × Fin 32) :
    monsterNortonCodeNineteenInverseShortCoefficient p.1 p.2 *
      nortonUIntegerSign (monsterNortonCodeNineteenShortUPhase p.1 p.2) =
        monsterNortonCodeNineteenForwardShortCoefficient
          (monsterNortonCodeNineteenShortUOutput p).1 (monsterNortonCodeNineteenShortUOutput
            p).2 := by
  revert p
  decide +kernel

/-- The full finite input Q evaluator at its certified physical octad coordinates. -/
def monsterNortonCodeNineteenShortUInputQ (p : Fin 8 × Fin 32) : Q :=
  monsterNortonOctadQSource
    (monsterNortonRemainingOctadUCodes (monsterNortonCodeNineteenInverseOctadChoice p.1))
    (monsterNortonRemainingOctadUPositions (monsterNortonCodeNineteenInverseOctadChoice p.1))
    (monsterNortonCodeNineteenInverseSign p.1 p.2)

/-- The finite input is exactly its original preferred source Q lift. -/
theorem monsterNortonCodeNineteenShortUInputQ_actual (p : Fin 8 × Fin 32) :
    monsterNortonShortQSource (monsterNortonCodeNineteenInverseShortIndex p) =
      monsterNortonCodeNineteenShortUInputQ p := by
  apply monsterNortonOctadQSource_actual
  exact monsterNortonRemainingOctadUPositions_actual _

/-- The full finite forward Q evaluator uses the actual increasing physical octad coordinates. -/
def monsterNortonCodeNineteenForwardShortQ (p : Fin 8 × Fin 32) : Q :=
  let a := monsterNortonCodeNineteenForwardOctadChoice p.1
  monsterNortonOctadQSource (monsterNortonEvenShortInverseUOctadCodes a)
    (monsterNortonEvenShortInverseUOctadPositions a) (monsterNortonCodeNineteenForwardSign p.1 p.2)

/-- The finite forward Q evaluator is the complete original preferred lift. -/
theorem monsterNortonCodeNineteenForwardShortQ_actual (p : Fin 8 × Fin 32) :
    monsterNortonShortQSource (monsterNortonCodeNineteenForwardShortIndex p) =
      monsterNortonCodeNineteenForwardShortQ p := by
  apply monsterNortonOctadQSource_actual
  exact monsterNortonEvenShortInverseUOctad_coordinate _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

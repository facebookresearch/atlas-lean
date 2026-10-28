/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact preferred-octad correspondence of inverse U on the code-sixteen short candidates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSixteenMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Complete actual inverse-U OutputOctad entries of the preferred-lift correspondence. -/
def monsterNortonCodeSixteenShortUOutputOctad : Fin 8 → Fin 32 → Fin 8 :=
  ![![2, 6, 5, 3, 3, 5, 6, 2,
    0, 7, 4, 1, 1, 4, 7, 0,
    0, 7, 4, 1, 1, 4, 7, 0,
    0, 7, 4, 1, 1, 4, 7, 0],
  ![2, 6, 5, 3, 3, 5, 6, 2,
    0, 7, 4, 1, 1, 4, 7, 0,
    0, 7, 4, 1, 1, 4, 7, 0,
    0, 7, 4, 1, 1, 4, 7, 0],
  ![0, 2, 7, 6, 4, 5, 1, 3,
    1, 3, 4, 5, 7, 6, 0, 2,
    2, 2, 6, 6, 5, 5, 3, 3,
    3, 3, 5, 5, 6, 6, 2, 2],
  ![0, 2, 2, 2, 1, 3, 3, 3,
    4, 5, 5, 5, 7, 6, 6, 6,
    2, 2, 2, 0, 3, 3, 3, 1,
    5, 5, 5, 4, 6, 6, 6, 7],
  ![0, 1, 2, 3, 4, 7, 5, 6,
    7, 4, 6, 5, 1, 0, 3, 2,
    2, 3, 2, 3, 5, 6, 5, 6,
    6, 5, 6, 5, 3, 2, 3, 2],
  ![2, 3, 5, 6, 6, 5, 3, 2,
    0, 1, 4, 7, 7, 4, 1, 0,
    0, 1, 4, 7, 7, 4, 1, 0,
    0, 1, 4, 7, 7, 4, 1, 0],
  ![2, 5, 6, 3, 0, 4, 7, 1,
    3, 6, 5, 2, 1, 7, 4, 0,
    0, 4, 7, 1, 0, 4, 7, 1,
    1, 7, 4, 0, 1, 7, 4, 0],
  ![0, 1, 2, 3, 7, 4, 6, 5,
    4, 7, 5, 6, 1, 0, 3, 2,
    2, 3, 2, 3, 6, 5, 6, 5,
    5, 6, 5, 6, 3, 2, 3, 2]]

/-- Complete actual inverse-U OutputSign entries of the preferred-lift correspondence. -/
def monsterNortonCodeSixteenShortUOutputSign : Fin 8 → Fin 32 → Fin 32 :=
  ![![13, 9, 12, 8, 15, 11, 14, 10,
    21, 17, 20, 16, 23, 19, 22, 18,
    26, 30, 27, 31, 24, 28, 25, 29,
    13, 9, 12, 8, 15, 11, 14, 10],
  ![15, 12, 14, 13, 10, 9, 11, 8,
    23, 20, 22, 21, 18, 17, 19, 16,
    24, 27, 25, 26, 29, 30, 28, 31,
    15, 12, 14, 13, 10, 9, 11, 8],
  ![5, 2, 1, 6, 4, 3, 0, 7,
    7, 0, 3, 4, 6, 1, 2, 5,
    21, 29, 17, 25, 20, 28, 16, 24,
    23, 31, 19, 27, 22, 30, 18, 26],
  ![7, 24, 16, 0, 5, 26, 18, 2,
    1, 30, 22, 6, 3, 28, 20, 4,
    7, 23, 31, 0, 5, 21, 29, 2,
    1, 17, 25, 6, 3, 19, 27, 4],
  ![6, 3, 1, 4, 0, 5, 7, 2,
    2, 7, 5, 0, 4, 1, 3, 6,
    22, 19, 30, 27, 16, 21, 24, 29,
    18, 23, 26, 31, 20, 17, 28, 25],
  ![14, 11, 8, 13, 10, 15, 12, 9,
    22, 19, 16, 21, 18, 23, 20, 17,
    25, 28, 31, 26, 29, 24, 27, 30,
    14, 11, 8, 13, 10, 15, 12, 9],
  ![12, 13, 8, 9, 27, 26, 31, 30,
    14, 15, 10, 11, 25, 24, 29, 28,
    12, 13, 8, 9, 20, 21, 16, 17,
    14, 15, 10, 11, 22, 23, 18, 19],
  ![4, 6, 3, 1, 7, 5, 0, 2,
    2, 0, 5, 7, 1, 3, 6, 4,
    20, 22, 28, 30, 23, 21, 31, 29,
    18, 16, 26, 24, 17, 19, 25, 27]]

/-- Complete actual inverse-U Phase entries of the preferred-lift correspondence. -/
def monsterNortonCodeSixteenShortUPhase : Fin 8 → Fin 32 → ZMod 2 :=
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
def monsterNortonCodeSixteenShortUOutput (p : Fin 8 × Fin 32) : Fin 8 × Fin 32 :=
  (monsterNortonCodeSixteenShortUOutputOctad p.1 p.2,
    monsterNortonCodeSixteenShortUOutputSign p.1 p.2)

/-- Every original forward short coordinate occurs exactly once. -/
theorem monsterNortonCodeSixteenShortUOutput_bijective :
    Function.Bijective monsterNortonCodeSixteenShortUOutput := by
  decide +kernel

/-- Full central phases preserve the exact normalized candidate coefficients. -/
theorem monsterNortonCodeSixteenShortU_coefficient (p : Fin 8 × Fin 32) :
    monsterNortonCodeSixteenInverseShortCoefficient p.1 p.2 *
      nortonUIntegerSign (monsterNortonCodeSixteenShortUPhase p.1 p.2) =
        monsterNortonCodeSixteenForwardShortCoefficient
          (monsterNortonCodeSixteenShortUOutput p).1 (monsterNortonCodeSixteenShortUOutput
            p).2 := by
  revert p
  decide +kernel

/-- The full finite input Q evaluator at its certified physical octad coordinates. -/
def monsterNortonCodeSixteenShortUInputQ (p : Fin 8 × Fin 32) : Q :=
  monsterNortonOctadQSource
    (monsterNortonRemainingOctadUCodes (monsterNortonCodeSixteenInverseOctadChoice p.1))
    (monsterNortonRemainingOctadUPositions (monsterNortonCodeSixteenInverseOctadChoice p.1))
    (monsterNortonCodeSixteenInverseSign p.1 p.2)

/-- The finite input is exactly its original preferred source Q lift. -/
theorem monsterNortonCodeSixteenShortUInputQ_actual (p : Fin 8 × Fin 32) :
    monsterNortonShortQSource (monsterNortonCodeSixteenInverseShortIndex p) =
      monsterNortonCodeSixteenShortUInputQ p := by
  apply monsterNortonOctadQSource_actual
  exact monsterNortonRemainingOctadUPositions_actual _

/-- The full finite forward Q evaluator uses the actual increasing physical octad coordinates. -/
def monsterNortonCodeSixteenForwardShortQ (p : Fin 8 × Fin 32) : Q :=
  let a := monsterNortonCodeSixteenForwardOctadChoice p.1
  monsterNortonOctadQSource (monsterNortonEvenShortInverseUOctadCodes a)
    (monsterNortonEvenShortInverseUOctadPositions a) (monsterNortonCodeSixteenForwardSign p.1 p.2)

/-- The finite forward Q evaluator is the complete original preferred lift. -/
theorem monsterNortonCodeSixteenForwardShortQ_actual (p : Fin 8 × Fin 32) :
    monsterNortonShortQSource (monsterNortonCodeSixteenForwardShortIndex p) =
      monsterNortonCodeSixteenForwardShortQ p := by
  apply monsterNortonOctadQSource_actual
  exact monsterNortonEvenShortInverseUOctad_coordinate _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

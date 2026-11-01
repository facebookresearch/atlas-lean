/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact preferred-octad correspondence of inverse U on the code-eighteen short candidates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeEighteenMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Complete actual inverse-U OutputOctad entries of the preferred-lift correspondence. -/
def monsterNortonCodeEighteenShortUOutputOctad : Fin 8 → Fin 32 → Fin 8 :=
  ![![2, 1, 5, 7, 0, 3, 4, 6,
    7, 5, 1, 2, 6, 4, 3, 0,
    0, 3, 4, 6, 0, 3, 4, 6,
    6, 4, 3, 0, 6, 4, 3, 0],
  ![2, 1, 5, 7, 0, 3, 4, 6,
    0, 3, 4, 6, 0, 3, 4, 6,
    7, 5, 1, 2, 6, 4, 3, 0,
    6, 4, 3, 0, 6, 4, 3, 0],
  ![0, 2, 6, 7, 4, 5, 3, 1,
    3, 1, 4, 5, 6, 7, 0, 2,
    2, 2, 7, 7, 5, 5, 1, 1,
    1, 1, 5, 5, 7, 7, 2, 2],
  ![0, 2, 2, 2, 3, 1, 1, 1,
    4, 5, 5, 5, 6, 7, 7, 7,
    2, 2, 2, 0, 1, 1, 1, 3,
    5, 5, 5, 4, 7, 7, 7, 6],
  ![0, 2, 2, 2, 6, 7, 7, 7,
    4, 5, 5, 5, 3, 1, 1, 1,
    2, 2, 2, 0, 7, 7, 7, 6,
    5, 5, 5, 4, 1, 1, 1, 3],
  ![2, 1, 5, 7, 7, 5, 1, 2,
    0, 3, 4, 6, 6, 4, 3, 0,
    0, 3, 4, 6, 6, 4, 3, 0,
    0, 3, 4, 6, 6, 4, 3, 0],
  ![2, 5, 7, 1, 0, 4, 6, 3,
    0, 4, 6, 3, 0, 4, 6, 3,
    1, 7, 5, 2, 3, 6, 4, 0,
    3, 6, 4, 0, 3, 6, 4, 0],
  ![0, 2, 2, 2, 4, 5, 5, 5,
    6, 7, 7, 7, 3, 1, 1, 1,
    2, 2, 2, 0, 5, 5, 5, 4,
    7, 7, 7, 6, 1, 1, 1, 3]]

/-- Complete actual inverse-U OutputSign entries of the preferred-lift correspondence. -/
def monsterNortonCodeEighteenShortUOutputSign : Fin 8 → Fin 32 → Fin 32 :=
  ![![13, 8, 11, 14, 10, 15, 12, 9,
    9, 12, 15, 10, 14, 11, 8, 13,
    26, 31, 28, 25, 18, 23, 20, 17,
    30, 27, 24, 29, 22, 19, 16, 21],
  ![15, 13, 9, 11, 8, 10, 14, 12,
    24, 26, 30, 28, 16, 18, 22, 20,
    12, 14, 10, 8, 11, 9, 13, 15,
    27, 25, 29, 31, 19, 17, 21, 23],
  ![5, 2, 1, 6, 4, 3, 0, 7,
    7, 0, 3, 4, 6, 1, 2, 5,
    26, 18, 30, 22, 27, 19, 31, 23,
    24, 16, 28, 20, 25, 17, 29, 21],
  ![7, 23, 31, 0, 5, 21, 29, 2,
    1, 17, 25, 6, 3, 19, 27, 4,
    7, 24, 16, 0, 5, 26, 18, 2,
    1, 30, 22, 6, 3, 28, 20, 4],
  ![6, 22, 30, 1, 5, 21, 29, 2,
    7, 23, 31, 0, 4, 20, 28, 3,
    6, 25, 17, 1, 5, 26, 18, 2,
    7, 24, 16, 0, 4, 27, 19, 3],
  ![14, 11, 8, 13, 10, 15, 12, 9,
    17, 20, 23, 18, 21, 16, 19, 22,
    9, 12, 15, 10, 13, 8, 11, 14,
    25, 28, 31, 26, 29, 24, 27, 30],
  ![12, 13, 8, 9, 11, 10, 15, 14,
    27, 26, 31, 30, 19, 18, 23, 22,
    14, 15, 10, 11, 9, 8, 13, 12,
    25, 24, 29, 28, 17, 16, 21, 20],
  ![4, 20, 28, 3, 5, 21, 29, 2,
    0, 16, 24, 7, 1, 17, 25, 6,
    4, 27, 19, 3, 5, 26, 18, 2,
    0, 31, 23, 7, 1, 30, 22, 6]]

/-- Complete actual inverse-U Phase entries of the preferred-lift correspondence. -/
def monsterNortonCodeEighteenShortUPhase : Fin 8 → Fin 32 → ZMod 2 :=
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
def monsterNortonCodeEighteenShortUOutput (p : Fin 8 × Fin 32) : Fin 8 × Fin 32 :=
  (monsterNortonCodeEighteenShortUOutputOctad p.1 p.2,
    monsterNortonCodeEighteenShortUOutputSign p.1 p.2)

/-- Every original forward short coordinate occurs exactly once. -/
theorem monsterNortonCodeEighteenShortUOutput_bijective :
    Function.Bijective monsterNortonCodeEighteenShortUOutput := by
  decide +kernel

/-- Full central phases preserve the exact normalized candidate coefficients. -/
theorem monsterNortonCodeEighteenShortU_coefficient (p : Fin 8 × Fin 32) :
    monsterNortonCodeEighteenInverseShortCoefficient p.1 p.2 *
      nortonUIntegerSign (monsterNortonCodeEighteenShortUPhase p.1 p.2) =
        monsterNortonCodeEighteenForwardShortCoefficient
          (monsterNortonCodeEighteenShortUOutput p).1 (monsterNortonCodeEighteenShortUOutput
            p).2 := by
  revert p
  decide +kernel

/-- The full finite input Q evaluator at its certified physical octad coordinates. -/
def monsterNortonCodeEighteenShortUInputQ (p : Fin 8 × Fin 32) : Q :=
  monsterNortonOctadQSource
    (monsterNortonRemainingOctadUCodes (monsterNortonCodeEighteenInverseOctadChoice p.1))
    (monsterNortonRemainingOctadUPositions (monsterNortonCodeEighteenInverseOctadChoice p.1))
    (monsterNortonCodeEighteenInverseSign p.1 p.2)

/-- The finite input is exactly its original preferred source Q lift. -/
theorem monsterNortonCodeEighteenShortUInputQ_actual (p : Fin 8 × Fin 32) :
    monsterNortonShortQSource (monsterNortonCodeEighteenInverseShortIndex p) =
      monsterNortonCodeEighteenShortUInputQ p := by
  apply monsterNortonOctadQSource_actual
  exact monsterNortonRemainingOctadUPositions_actual _

/-- The full finite forward Q evaluator uses the actual increasing physical octad coordinates. -/
def monsterNortonCodeEighteenForwardShortQ (p : Fin 8 × Fin 32) : Q :=
  let a := monsterNortonCodeEighteenForwardOctadChoice p.1
  monsterNortonOctadQSource (monsterNortonEvenShortInverseUOctadCodes a)
    (monsterNortonEvenShortInverseUOctadPositions a) (monsterNortonCodeEighteenForwardSign p.1 p.2)

/-- The finite forward Q evaluator is the complete original preferred lift. -/
theorem monsterNortonCodeEighteenForwardShortQ_actual (p : Fin 8 × Fin 32) :
    monsterNortonShortQSource (monsterNortonCodeEighteenForwardShortIndex p) =
      monsterNortonCodeEighteenForwardShortQ p := by
  apply monsterNortonOctadQSource_actual
  exact monsterNortonEvenShortInverseUOctad_coordinate _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

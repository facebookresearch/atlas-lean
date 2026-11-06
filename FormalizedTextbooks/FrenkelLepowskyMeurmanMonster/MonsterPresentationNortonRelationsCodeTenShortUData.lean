/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full preferred-pair source correspondence for basis ten's inverse short U transport. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTenMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete actual inverse-U OutputCode table for all supported preferred pairs. -/
def monsterNortonCodeTenShortUOutputCode : Fin 2 → Fin 128 → Fin 32 :=
  ![![30, 30, 30, 30, 30, 30, 30, 30,
    6, 6, 6, 6, 6, 6, 6, 6,
    18, 12, 13, 11, 10, 20, 19, 21,
    24, 0, 25, 1, 31, 7, 18, 12,
    13, 11, 10, 20, 19, 21, 24, 0,
    25, 1, 31, 7, 18, 18, 18, 18,
    18, 18, 12, 12, 12, 12, 12, 12,
    13, 13, 13, 13, 13, 13, 11, 11,
    11, 11, 11, 11, 10, 10, 10, 10,
    10, 10, 20, 20, 20, 20, 20, 20,
    19, 19, 19, 19, 19, 19, 21, 21,
    21, 21, 21, 21, 24, 24, 24, 24,
    24, 24, 0, 0, 0, 0, 0, 0,
    25, 1, 31, 7, 25, 1, 31, 7,
    25, 25, 25, 25, 1, 31, 7, 1,
    31, 7, 1, 1, 31, 31, 7, 7],
  ![26, 26, 26, 26, 26, 26, 26, 26,
    2, 2, 2, 2, 2, 2, 2, 2,
    22, 8, 9, 15, 14, 16, 23, 17,
    28, 4, 29, 5, 27, 3, 22, 8,
    9, 15, 14, 16, 23, 17, 28, 4,
    29, 5, 27, 3, 22, 22, 22, 22,
    22, 22, 8, 8, 8, 8, 8, 8,
    9, 9, 9, 9, 9, 9, 15, 15,
    15, 15, 15, 15, 14, 14, 14, 14,
    14, 14, 16, 16, 16, 16, 16, 16,
    23, 23, 23, 23, 23, 23, 17, 17,
    17, 17, 17, 17, 28, 28, 28, 28,
    28, 28, 4, 4, 4, 4, 4, 4,
    29, 5, 27, 3, 29, 5, 27, 3,
    29, 29, 29, 29, 5, 27, 3, 5,
    27, 3, 5, 5, 27, 27, 3, 3]]

/-- The complete actual inverse-U OutputColumn table for all supported preferred pairs. -/
def monsterNortonCodeTenShortUOutputColumn : Fin 2 → Fin 128 → Fin 8 :=
  ![![4, 0, 5, 2, 7, 3, 1, 6,
    4, 0, 5, 2, 7, 3, 1, 6,
    4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 5, 2, 7, 3,
    1, 6, 5, 2, 7, 3, 1, 6,
    5, 2, 7, 3, 1, 6, 5, 2,
    7, 3, 1, 6, 5, 2, 7, 3,
    1, 6, 5, 2, 7, 3, 1, 6,
    5, 2, 7, 3, 1, 6, 5, 2,
    7, 3, 1, 6, 5, 2, 7, 3,
    1, 6, 5, 2, 7, 3, 1, 6,
    5, 5, 5, 5, 2, 2, 2, 2,
    7, 3, 1, 6, 7, 7, 7, 3,
    3, 3, 1, 6, 1, 6, 1, 6],
  ![4, 0, 5, 2, 7, 3, 1, 6,
    4, 0, 5, 2, 7, 3, 1, 6,
    4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 5, 2, 7, 3,
    1, 6, 5, 2, 7, 3, 1, 6,
    5, 2, 7, 3, 1, 6, 5, 2,
    7, 3, 1, 6, 5, 2, 7, 3,
    1, 6, 5, 2, 7, 3, 1, 6,
    5, 2, 7, 3, 1, 6, 5, 2,
    7, 3, 1, 6, 5, 2, 7, 3,
    1, 6, 5, 2, 7, 3, 1, 6,
    5, 5, 5, 5, 2, 2, 2, 2,
    7, 3, 1, 6, 7, 7, 7, 3,
    3, 3, 1, 6, 1, 6, 1, 6]]

/-- The complete actual inverse-U Phase table for all supported preferred pairs. -/
def monsterNortonCodeTenShortUPhase : Fin 2 → Fin 128 → ZMod 2 :=
  ![![1, 1, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 1, 1, 1, 1, 1,
    0, 1, 1, 1, 0, 1, 1, 1,
    0, 1, 0, 1, 0, 1, 0, 1,
    1, 1, 0, 1, 1, 1, 0, 1,
    0, 1, 0, 1, 1, 1, 1, 1,
    1, 1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1, 1, 1, 1,
    1, 1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1, 1, 1, 1,
    1, 1, 0, 0, 0, 0, 0, 0,
    1, 0, 1, 0, 1, 0, 1, 0,
    1, 1, 1, 1, 0, 1, 0, 0,
    1, 0, 0, 0, 1, 1, 0, 0],
  ![0, 0, 1, 1, 1, 1, 1, 1,
    1, 1, 0, 0, 0, 0, 0, 0,
    1, 0, 0, 0, 1, 0, 0, 0,
    1, 0, 1, 0, 1, 0, 1, 0,
    0, 0, 1, 0, 0, 0, 1, 0,
    1, 0, 1, 0, 0, 0, 0, 0,
    0, 0, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 0, 0, 0, 0,
    0, 0, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 0, 0, 0, 0,
    0, 0, 1, 1, 1, 1, 1, 1,
    0, 1, 0, 1, 0, 1, 0, 1,
    0, 0, 0, 0, 1, 0, 1, 1,
    0, 1, 1, 1, 0, 0, 1, 1]]

/-- The exact forward odd coordinate of each inverse pair under inverse U. -/
def monsterNortonCodeTenShortUOutput (p : Fin 2 × Fin 128) : Fin 32 × Fin 8 :=
  (monsterNortonCodeTenShortUOutputCode p.1 p.2,
    monsterNortonCodeTenShortUOutputColumn p.1 p.2)

/-- All supported inverse pairs account for every forward odd entry exactly once. -/
theorem monsterNortonCodeTenShortUOutput_bijective :
    Function.Bijective monsterNortonCodeTenShortUOutput := by
  decide +kernel

/-- Every full central sign gives the exact forward short coefficient. -/
theorem monsterNortonCodeTenShortU_coefficient (p : Fin 2 × Fin 128) :
    monsterNortonCodeTenInverseShortCoefficient p.1 p.2 *
      nortonUIntegerSign (monsterNortonCodeTenShortUPhase p.1 p.2) =
        monsterNortonCodeTenForwardShortCoefficient
          (monsterNortonCodeTenShortUOutput p).1 (monsterNortonCodeTenShortUOutput p).2 := by
  revert p
  decide +kernel

/-- The complete preferred lift evaluated directly from the physical pair coordinates. -/
def monsterNortonCodeTenShortUInputQ (p : Fin 2 × Fin 128) : Q :=
  ⟨ofAdd (Fin.append (if p.1 = 0 then 0 else Pi.single 11 1)
    (fun k => (golayGeneratorBit k (monsterNortonCodeTenInversePairFirst p.2) : ZMod 2) +
      golayGeneratorBit k (monsterNortonCodeTenInversePairSecond p.2))), 1⟩

/-- This finite evaluator is the genuine full preferred source Q lift. -/
theorem monsterNortonCodeTenShortUInputQ_actual (p : Fin 2 × Fin 128) :
    monsterNortonShortQSource (monsterNortonCodeTenInverseShortIndex p) =
      monsterNortonCodeTenShortUInputQ p := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change Fin.append (if p.1 = 0 then 0 else Pi.single 11 1)
      (griessPairSyndrome (monsterNortonCodeTenInversePair p.2)) =
      Fin.append (if p.1 = 0 then 0 else Pi.single 11 1)
        (fun k => (golayGeneratorBit k (monsterNortonCodeTenInversePairFirst p.2) : ZMod 2) +
          golayGeneratorBit k (monsterNortonCodeTenInversePairSecond p.2))
    congr 1
    funext k
    change (golayGeneratorBit k (griessCoordinatePair (monsterNortonCodeTenInversePair p.2)).1 :
      ZMod 2) + golayGeneratorBit k (griessCoordinatePair
        (monsterNortonCodeTenInversePair p.2)).2 = _
    rw [monsterNortonCodeTenInversePair, griessPairIndex_coordinates,
      ite_eq_left (monsterNortonCodeTenInversePair_lt p.2)]
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

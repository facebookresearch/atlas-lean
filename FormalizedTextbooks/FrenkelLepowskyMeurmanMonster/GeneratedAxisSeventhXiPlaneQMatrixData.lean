/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneQAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortHom

/-! Literal full binary and central-phase matrices for the genuine corrected Xi action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Full binary image columns; both translation and modulation coordinates are retained. -/
def generatedSeventhXiPlaneQColumns : Fin 24 → ℕ :=
  ![
    3539863, 13576413, 14295259, 6098952, 3647510, 9598965,
    10737557, 1411206, 1646830, 721022, 16723791, 4612096,
    6144, 1271564, 1802, 3148694, 3115496, 2196368,
    2591632, 330360, 918142, 1933806, 5439494, 13181145]

/-- Upper-triangular quadratic central-phase coefficients, including all diagonal linear terms. -/
def generatedSeventhXiPlaneQPhaseRows : Fin 24 → ℕ :=
  ![
    12125190, 12857584, 12865984, 2588888, 15607520, 9639872,
    16594176, 12125824, 7217408, 0, 16593920, 8388608,
    8392704, 8396800, 16384, 3735552, 2031616, 3801088,
    12058624, 2621440, 2097152, 0, 8388608, 8388608]

/-- The full binary coordinate matrix, using the actual bit convention of Q. -/
def generatedSeventhXiPlaneQMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) := fun i j =>
  golayBooleanCast ((generatedSeventhXiPlaneQColumns j).testBit i.val)

/-- Central coefficients in the same actual coordinate basis. -/
def generatedSeventhXiPlaneQPhaseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) := fun i j =>
  golayBooleanCast ((generatedSeventhXiPlaneQPhaseRows i).testBit j.val)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Separately checked full-Q stages of the exact Singer/U intertwining certificate. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQImageCache

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Binary coordinate masks after P, UP, U²P and U³P, in actual hyperbolic coordinates. -/
def monsterNortonSingerUCoordinateMasks : Fin 4 → Fin 24 → ℕ :=
![
  ![0xf, 0x80b, 0x807, 0x80d, 0x200, 0x300, 0x10, 0x20,
    0xc0, 0x40, 0xc0f, 0x800, 0x40e000, 0x5000, 0x9000, 0x3000,
    0x300000, 0x100000, 0x10000, 0x20000, 0x80000, 0xc0000, 0x400000, 0xc0f000],
  ![0x47b900, 0x4d7200, 0x4d7300, 0xd6100, 0x40e84c, 0x1050, 0x40f83a, 0x40e88a,
    0x10e0, 0x40f826, 0xad7400, 0x401900, 0xe6, 0x9019b4, 0xb019b4, 0x2009ba,
    0xa000e, 0x8cc0f, 0x4ac0f, 0x3ac01, 0x16c01, 0xd000e, 0x900, 0x2004e8],
  ![0x9b944f, 0xf95d1f, 0xb9a503, 0xf94413, 0xe0c0, 0x40, 0x1b0a, 0x40e320,
    0x40f836, 0x40e230, 0x31a000, 0xe840, 0xeb6a, 0x22036b, 0x20cf6a, 0x2c76b,
    0x80000, 0x8c1801, 0x310801, 0x30a400, 0x130801, 0x36c01, 0xe11c, 0xa2336b],
  ![0x3328c0, 0x12a0c0, 0x124040, 0x124080, 0x1906, 0x40f826, 0x1b0c, 0x40f83c,
    0x1a0a, 0x40f81a, 0x9ebc0f, 0xe8c0, 0x21a, 0xc0bfc, 0x8813fd, 0x8413fd,
    0x16c01, 0x206400, 0x3cc01, 0x30c400, 0x2ac01, 0x10a400, 0x8c0, 0xc0614]
]

/-- The exact central signs at each separately checked coordinate stage. -/
def monsterNortonSingerUCoordinatePhases : Fin 4 → Fin 24 → Bool :=
![
  ![false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false],
  ![false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false],
  ![true, false, true, true, false, false, false, false,
    false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false],
  ![false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false]
]

/-- Full Q coordinate-stage elements with the stated binary coordinates and central coefficients. -/
def monsterNortonSingerUCoordinate (k : Fin 4) (i : Fin 24) : Q :=
  ⟨ofAdd (fun j => if (monsterNortonSingerUCoordinateMasks k i).testBit j.val then 1 else 0),
    ofAdd (if monsterNortonSingerUCoordinatePhases k i then 1 else 0)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- Check all twenty-four full coordinate images of the actual source permutation.
/-- The initial table is the actual Singer image of each positive coordinate lift. -/
theorem monsterNortonSingerUCoordinate_initial (i : Fin 24) :
    monsterNortonSingerImage (qCoordinateGenerator i) = monsterNortonSingerUCoordinate 0 i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change (fun j : Fin 24 => toAdd
      (monsterNortonSingerImage (qCoordinateGenerator i)).base j) =
        (fun j : Fin 24 => toAdd (monsterNortonSingerUCoordinate 0 i).base j)
    fin_cases i <;> decide +kernel
  · apply toAdd.injective
    fin_cases i <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- Check each of the seventy-two U transitions with its complete actual cached central phase.
/-- Every adjacent pair of tables is related by the genuine Norton U conjugation evaluator. -/
theorem monsterNortonSingerUCoordinate_step (k : Fin 3) (i : Fin 24) :
    monsterNortonUQFastImage (monsterNortonSingerUCoordinate (Fin.castAdd 1 k) i) =
      monsterNortonSingerUCoordinate (Fin.natAdd 1 k) i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change (fun j : Fin 24 => toAdd
      (monsterNortonUQFastImage (monsterNortonSingerUCoordinate (Fin.castAdd 1 k) i)).base j) =
        (fun j : Fin 24 => toAdd (monsterNortonSingerUCoordinate (Fin.natAdd 1 k) i).base j)
    fin_cases k <;> fin_cases i <;> decide +kernel
  · apply toAdd.injective
    fin_cases k <;> fin_cases i <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- Check all complete target images, retaining the actual source phase of U's coordinate lifts.
/-- The final table is also the actual Singer image of each U coordinate image. -/
theorem monsterNortonSingerUCoordinate_target (i : Fin 24) :
    monsterNortonSingerImage (monsterNortonUQGeneratorImage i) =
      monsterNortonSingerUCoordinate 3 i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change (fun j : Fin 24 => toAdd
      (monsterNortonSingerImage (monsterNortonUQGeneratorImage i)).base j) =
        (fun j : Fin 24 => toAdd (monsterNortonSingerUCoordinate 3 i).base j)
    fin_cases i <;> decide +kernel
  · apply toAdd.injective
    fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

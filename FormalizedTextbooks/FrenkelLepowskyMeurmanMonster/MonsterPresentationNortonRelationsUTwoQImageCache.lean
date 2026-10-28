/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full binary and central-phase cache for the actual squared Norton conjugation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQImageCache

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The twenty-four binary masks of the actual squared source word. -/
def monsterNortonUTwoQGeneratorMasks : Fin 24 → ℕ :=
  ![0xb9544f, 0x62381c, 0x622110, 0x22d90c, 0x1b0a, 0x40e320,
    0x40e230, 0x1a06, 0xe080, 0xe0c0, 0xaadc0f, 0xe840,
    0x11c, 0x2c677, 0x220277, 0x20ce76, 0x310801, 0x30a400,
    0x106400, 0x130801, 0x8c1801, 0x841801, 0xe11c, 0xa2d91d]

/-- The full lift phases; the first generator image has its actual negative central sign. -/
def monsterNortonUTwoQGeneratorPhase : Fin 24 → ZMod 2 :=
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Full coordinate-model images with every computed lift phase retained. -/
def monsterNortonUTwoQGeneratorImage (i : Fin 24) : Q :=
  ⟨ofAdd (fun j => if (monsterNortonUTwoQGeneratorMasks i).testBit j.val then 1 else 0),
    ofAdd (monsterNortonUTwoQGeneratorPhase i)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 80000000 in
-- Check all coordinates and central signs through the already proved full-phase U evaluator.
/-- Every cached image equals the complete actual two-step source conjugation. -/
theorem monsterNortonUTwoQGeneratorImage_certificate (i : Fin 24) :
    monsterNortonUQFastImage (monsterNortonUQGeneratorImage i) =
      monsterNortonUTwoQGeneratorImage i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change (fun j : Fin 24 =>
      toAdd (monsterNortonUQFastImage (monsterNortonUQGeneratorImage i)).base j) =
      (fun j : Fin 24 => toAdd (monsterNortonUTwoQGeneratorImage i).base j)
    fin_cases i <;> decide +kernel
  · apply toAdd.injective
    change toAdd (monsterNortonUQFastImage (monsterNortonUQGeneratorImage i)).coeff =
      monsterNortonUTwoQGeneratorPhase i
    fin_cases i <;> decide +kernel

/-- The finite certificate is genuine squared spin conjugation on all positive coordinate lifts. -/
theorem monsterNortonUTwoQGeneratorImage_actual (i : Fin 24) :
    spinConjugation (monsterNortonUFiber.val.1 ^ 2) (qCoordinateGenerator i) =
      monsterNortonUTwoQGeneratorImage i := by
  rw [pow_two, map_mul]
  change spinConjugation monsterNortonUFiber.val.1
    (spinConjugation monsterNortonUFiber.val.1 (qCoordinateGenerator i)) = _
  rw [monsterNortonUQImage_eq (qCoordinateGenerator i),
    monsterNortonUQGeneratorImage_certificate, monsterNortonUQImage_eq,
    monsterNortonUQFastImage_eq]
  exact monsterNortonUTwoQGeneratorImage_certificate i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

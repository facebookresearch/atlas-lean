/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A finite, full-phase cache of actual Norton u conjugation on Q. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQCoordinateEvaluation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQImage

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Actual binary images of the twenty-four positive coordinate lifts. -/
def monsterNortonUQGeneratorMasks : Fin 24 → ℕ :=
  ![0x4d7900, 0xac100, 0x4ad200, 0x4ad300, 0x40f83a, 0x40e88a,
    0x40f826, 0x40e8c6, 0x40f81c, 0x40e84c, 0xaad400, 0x401900,
    0x5c, 0x2009e6, 0x9019e8, 0xb019e8, 0x4ac0f, 0x3ac01,
    0xc6c0f, 0x16c01, 0x8cc0f, 0x2cc01, 0x900, 0x200452]

/-- The full actual generator images; the checked source word gives central coefficient zero. -/
def monsterNortonUQGeneratorImage (i : Fin 24) : Q :=
  ⟨ofAdd (fun j => if (monsterNortonUQGeneratorMasks i).testBit j.val then 1 else 0), 1⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 80000000 in
-- Check all 24 complete Q images through the actual seven source factors, including central phases.
/-- Every cached lift equals the actual source Norton Q image, with its full central sign. -/
theorem monsterNortonUQGeneratorImage_certificate (i : Fin 24) :
    monsterNortonUQImage (qCoordinateGenerator i) = monsterNortonUQGeneratorImage i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change (fun j : Fin 24 => toAdd (monsterNortonUQImage (qCoordinateGenerator i)).base j) =
      (fun j : Fin 24 => toAdd (monsterNortonUQGeneratorImage i).base j)
    fin_cases i <;> decide +kernel
  · apply toAdd.injective
    change toAdd (monsterNortonUQImage (qCoordinateGenerator i)).coeff = (0 : ZMod 2)
    fin_cases i <;> decide +kernel

/-- The compact full-phase evaluator of the actual Norton action. -/
def monsterNortonUQFastImage (q : Q) : Q :=
  monsterNortonCoordinateEvaluation monsterNortonUQGeneratorImage q

/-- The compact evaluator agrees with the genuine complete Norton Q conjugation for every input. -/
theorem monsterNortonUQFastImage_eq (q : Q) :
    monsterNortonUQImage q = monsterNortonUQFastImage q := by
  rw [← monsterNortonUQImage_eq]
  apply monsterNortonCoordinateEvaluation_eq
  intro i
  rw [monsterNortonUQImage_eq]
  exact monsterNortonUQGeneratorImage_certificate i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

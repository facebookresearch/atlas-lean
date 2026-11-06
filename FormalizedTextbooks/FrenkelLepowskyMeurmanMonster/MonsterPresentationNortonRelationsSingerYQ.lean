/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact source-code Y covariance under the Singer spin permutation on the preferred basis. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsYSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.QCoordinateGenerators

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The eleven low source-code basis labels. -/
def monsterNortonSingerYBasisSource (a : Fin 11) : Fin 2048 :=
  ⟨2 ^ a.val, by fin_cases a <;> decide⟩

/-- The low components of their actual permuted code labels. -/
def monsterNortonSingerYBasisTarget : Fin 11 → Fin 2048 :=
  ![15, 11, 7, 13, 512, 768, 16, 32, 192, 64, 1039]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- Check the complete central-corrected images of all 264 actual Q coordinate lifts.
/-- The Singer permutation intertwines the two actual Y conjugation maps on each coordinate lift. -/
theorem monsterNortonSingerY_basis_coordinate_certificate (a : Fin 11) (i : Fin 24) :
    monsterNortonSingerImage
      (monsterNortonYImage (monsterNortonSingerYBasisSource a) (qCoordinateGenerator i)) =
      monsterNortonYImage (monsterNortonSingerYBasisTarget a)
        (monsterNortonSingerImage (qCoordinateGenerator i)) := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change (fun j : Fin 24 => toAdd
      (monsterNortonSingerImage (monsterNortonYImage
        (monsterNortonSingerYBasisSource a) (qCoordinateGenerator i))).base j) =
      (fun j : Fin 24 => toAdd
        (monsterNortonYImage (monsterNortonSingerYBasisTarget a)
          (monsterNortonSingerImage (qCoordinateGenerator i))).base j)
    fin_cases a <;> fin_cases i <;> decide +kernel
  · apply toAdd.injective
    fin_cases a <;> fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

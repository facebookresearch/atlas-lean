/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full actual Q phase checks for all basis-ten inverse short coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTenShortUData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQSelectedPhase

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 48000000 in
-- Check each full 24-coordinate and central-phase source image in the ordinary kernel.
/-- The full genuine inverse-U cache sends every candidate source lift to its exact output. -/
theorem monsterNortonCodeTenShortU_source_certificate (i : Fin 2) (j : Fin 128) :
    monsterNortonUQInverseFastImage (monsterNortonCodeTenShortUInputQ (i, j)) =
      qCentral (monsterNortonCodeTenShortUPhase i j) *
        monsterNortonShortQSource
          (monsterNortonCodeTenForwardShortIndex (monsterNortonCodeTenShortUOutput (i, j)))
      := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply Multiplicative.toAdd.injective
    change (fun k : Fin 24 => toAdd
      (monsterNortonUQInverseFastImage (monsterNortonCodeTenShortUInputQ (i, j))).base k) =
      (fun k : Fin 24 => toAdd
        (qCentral (monsterNortonCodeTenShortUPhase i j) *
          monsterNortonShortQSource
            (monsterNortonCodeTenForwardShortIndex
              (monsterNortonCodeTenShortUOutput (i, j)))).base k)
    fin_cases i <;> revert j <;> decide +kernel
  · apply Multiplicative.toAdd.injective
    rw [monsterNortonUQInverseFastImage_selected_phase]
    fin_cases i <;> revert j <;> decide +kernel

/-- All original inverse short basis vectors have their complete actual inverse-U image. -/
theorem monsterNortonCodeTenShortU_actual (p : Fin 2 × Fin 128) :
    (y555NortonActualU⁻¹).val
      (griessConwayDecode (0, (Pi.single (monsterNortonCodeTenInverseShortIndex p) 1, 0))) =
        griessConwayDecode (0,
          (qSign (monsterNortonCodeTenShortUPhase p.1 p.2) •
            Pi.single (monsterNortonCodeTenForwardShortIndex
              (monsterNortonCodeTenShortUOutput p)) 1, 0)) := by
  apply monsterNortonU_inverse_short_basis_of_source_certificate
  rw [monsterNortonCodeTenShortUInputQ_actual]
  exact monsterNortonCodeTenShortU_source_certificate p.1 p.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full actual Q phase checks for all code-seventeen inverse short coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSeventeenShortUData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQSelectedPhase

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 48000000 in
-- Check each full 24-coordinate and central-phase source image in the ordinary kernel.
/-- The full genuine inverse-U cache sends every candidate source lift to its exact output. -/
theorem monsterNortonCodeSeventeenShortU_source_certificate (i : Fin 8) (j : Fin 32) :
    monsterNortonUQInverseFastImage (monsterNortonCodeSeventeenShortUInputQ (i, j)) =
      qCentral (monsterNortonCodeSeventeenShortUPhase i j) *
        monsterNortonShortQSource
          (monsterNortonCodeSeventeenForwardShortIndex
            (monsterNortonCodeSeventeenShortUOutput (i, j)))
      := by
  rw [monsterNortonCodeSeventeenForwardShortQ_actual]
  apply NormalizedCocycleExtension.Extension.ext
  · apply Multiplicative.toAdd.injective
    change (fun k : Fin 24 => toAdd
      (monsterNortonUQInverseFastImage (monsterNortonCodeSeventeenShortUInputQ (i, j))).base k) =
      (fun k : Fin 24 => toAdd
        (qCentral (monsterNortonCodeSeventeenShortUPhase i j) *
          monsterNortonCodeSeventeenForwardShortQ
            (monsterNortonCodeSeventeenShortUOutput (i, j))).base k)
    fin_cases i <;> revert j <;> decide +kernel
  · apply Multiplicative.toAdd.injective
    rw [monsterNortonUQInverseFastImage_selected_phase]
    fin_cases i <;> revert j <;> decide +kernel

/-- All original inverse short basis vectors have their complete actual inverse-U image. -/
theorem monsterNortonCodeSeventeenShortU_actual (p : Fin 8 × Fin 32) :
    (y555NortonActualU⁻¹).val
      (griessConwayDecode (0, (Pi.single (monsterNortonCodeSeventeenInverseShortIndex p) 1, 0))) =
        griessConwayDecode (0,
          (qSign (monsterNortonCodeSeventeenShortUPhase p.1 p.2) •
            Pi.single (monsterNortonCodeSeventeenForwardShortIndex
              (monsterNortonCodeSeventeenShortUOutput p)) 1, 0)) := by
  apply monsterNortonU_inverse_short_basis_of_source_certificate
  rw [monsterNortonCodeSeventeenShortUInputQ_actual]
  exact monsterNortonCodeSeventeenShortU_source_certificate p.1 p.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

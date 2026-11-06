/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual Q conjugation certificates for the remaining original octad inputs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsRemainingOctadUCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQSelectedPhaseForward

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 128000000 in
-- Check all binary coordinates and central phases through the proved actual Q-action cache.
/-- Every displayed preferred output is the full actual Q image, including its central sign. -/
theorem monsterNortonRemainingOctadU_certificate (k : Fin 10) (e : Fin 64) :
    monsterNortonUQFastImage (monsterNortonRemainingOctadUInputQ k e) =
      qCentral (monsterNortonRemainingOctadUPhase k e) *
        monsterNortonRemainingOctadUOutputQ k e := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change (fun i : Fin 24 => toAdd
      (monsterNortonUQFastImage (monsterNortonRemainingOctadUInputQ k e)).base i) =
      (fun i : Fin 24 => toAdd
        (qCentral (monsterNortonRemainingOctadUPhase k e) *
          monsterNortonRemainingOctadUOutputQ k e).base i)
    fin_cases k <;> revert e <;> decide +kernel
  · apply toAdd.injective
    rw [monsterNortonUQFastImage_selected_phase]
    fin_cases k <;> revert e <;> decide +kernel

/-- The certified complete Q image gives the full actual Griess short-unit transport. -/
theorem monsterNortonRemainingOctadU_actual (k : Fin 10) (e : Fin 64) :
    y555NortonActualU.val
      (griessConwayDecode (0, (Pi.single (monsterNortonRemainingOctadUInput k e) 1, 0))) =
      griessConwayDecode (0, (qSign (monsterNortonRemainingOctadUPhase k e) •
        Pi.single (monsterNortonRemainingOctadUOutput k e) 1, 0)) := by
  apply monsterNortonU_short_basis_of_source_certificate
  rw [monsterNortonRemainingOctadUInputQ_actual, monsterNortonRemainingOctadUOutputQ_actual]
  exact monsterNortonRemainingOctadU_certificate k e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

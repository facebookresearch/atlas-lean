/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact source Singer permutation fixes the literal Norton involution V. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonConjugation

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check the complete source Q coordinates and central phase of the involution V.
/-- The exact spin permutation fixes V as a full Q element, including its source phase. -/
theorem monsterNortonSinger_VQ_certificate :
    monsterNortonSingerImage y555NortonVQ = y555NortonVQ := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change (fun j : Fin 24 => toAdd (monsterNortonSingerImage y555NortonVQ).base j) =
      (fun j : Fin 24 => toAdd y555NortonVQ.base j)
    decide +kernel
  · apply toAdd.injective
    decide +kernel

/-- The actual forward local lift commutes with Norton V. -/
theorem monsterNortonSingerLocal_generated_commute_V :
    Commute (localIntoGenerated monsterNortonSingerLocal) y555NortonV := by
  have h := monsterFiberGenerated_conjugate_Q monsterNortonSingerFiber y555NortonVQ
  change localIntoGenerated monsterNortonSingerLocal * y555NortonV *
      (localIntoGenerated monsterNortonSingerLocal)⁻¹ =
    qIntoGenerated (spinConjugation monsterNortonSingerSpin y555NortonVQ) at h
  rw [monsterNortonSingerSpin_conjugation, monsterNortonSinger_VQ_certificate] at h
  change _ = y555NortonV at h
  exact mul_inv_eq_iff_eq_mul.mp h

/-- The actual source inverse permutation also commutes with Norton V. -/
theorem monsterNortonSingerGenerated_commute_V :
    Commute monsterNortonSingerGenerated y555NortonV := by
  simpa only [monsterNortonSingerGenerated, map_inv] using
    monsterNortonSingerLocal_generated_commute_V.inv_left

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

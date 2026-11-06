/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full actual central phases of inverse U on every reached octad Fourier packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseUData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseUInputQ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQSelectedPhase

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 64000000 in
-- Check all 1472 complete central coefficients through the actual certified inverse-U spin cache.
/-- Each displayed preferred-lift phase is the true actual spin-conjugation central coefficient. -/
theorem monsterNortonEvenShortInverseUPhase_actual (k : Fin 23) (e : Fin 64) :
    toAdd (spinConjugation (monsterNortonUFiber⁻¹).val.1
      (monsterNortonShortQ (monsterNortonEvenShortInverseUInput k e))).coeff =
        monsterNortonEvenShortInverseUPhase k e := by
  rw [monsterNortonUQInverseFastImage_eq]
  rw [monsterNortonEvenShortInverseUInputQ_actual]
  rw [monsterNortonUQInverseFastImage_selected_phase]
  revert k e
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

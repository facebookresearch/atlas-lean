/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthOddRootData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthQImage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortLookup

/-! Exact central phases of the actual inverse source word on its 64 odd roots.
The finite bits are checked against the full actual preferred-Q conjugation
formula, rather than assigned from a modular discovery representation. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- The full preferred-Q central coefficients, in the verified odd-root ordering. -/
def generatedFifthOddRootPhaseData : Fin 64 → ZMod 2 :=
  ![0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0,
    1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0,
    1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1,
    1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Evaluate the exact four-factor actual source conjugation at all 64 preferred odd lifts.
/-- Every finite phase is the central coefficient of the genuine full-Q image. -/
theorem generatedFifth_odd_phase_certificate : ∀ j : Fin 64,
    toAdd (generatedFifthInverseQImage
      (monsterNortonShortQ (generatedFifthOddRootOutputLabel j))).coeff =
        generatedFifthOddRootPhaseData j := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

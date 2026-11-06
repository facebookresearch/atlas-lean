/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthOddRootData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLocalWord

/-! Exact central phases of the actual inverse source word on its 56 odd roots.
The finite bits are checked against the full actual preferred-Q conjugation
formula, rather than assigned from a modular discovery representation. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- The full preferred-Q central coefficients, in the verified odd-root ordering. -/
def generatedFourthOddRootPhaseData : Fin 56 → ZMod 2 :=
  ![0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1,
    0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1,
    1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1,
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Evaluate the exact three-factor actual source conjugation at all 56 preferred odd lifts.
/-- Every finite phase is the central coefficient of the genuine full-Q image. -/
theorem generatedFourth_odd_phase_certificate : ∀ j : Fin 56,
    toAdd (generatedFourthInverseQImage
      (monsterNortonShortQ (generatedFourthOddRootOutputLabel j))).coeff =
        generatedFourthOddRootPhaseData j := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

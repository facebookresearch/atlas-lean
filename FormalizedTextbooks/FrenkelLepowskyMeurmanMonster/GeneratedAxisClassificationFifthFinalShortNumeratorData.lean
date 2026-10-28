/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthFinalShortSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMiddleProjector

/-! Executable integer numerators for the actual final fifth-axis short coefficients. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The finite original preferred-Q and input phases of the 56 middle octad rows. -/
def generatedFifthEvenCoefficientCache : Fin 56 → ZMod 2 :=
  ![0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0,
    1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
    1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0,
    1, 1, 0, 0, 0, 0, 1, 1]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Evaluate the genuine four-factor inverse conjugation, retaining its central coefficient.
/-- Each cached coefficient bit is the genuine source and preferred-Q phase. -/
theorem generatedFifth_even_coefficient_cache : ∀ j : Fin 56,
    generatedFifthEvenCoefficientPhase j = generatedFifthEvenCoefficientCache j := by
  unfold generatedFifthEvenCoefficientPhase generatedFifthEvenRootPhase
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

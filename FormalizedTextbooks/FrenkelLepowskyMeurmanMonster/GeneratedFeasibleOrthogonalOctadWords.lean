/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GriessCoordinates

/-! Finite original Golay word and sign-pattern checks for physical root orthogonality.
These are source-coordinate counts, before the complete axis-transition classification. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Actual encoded octad words omitting both coordinates of the fixed root. -/
def generatedFeasibleOctadsOutsideRootPair : Finset (Fin 4096) :=
  Finset.univ.filter fun d => golayMaskWeight (golayEncodedMask d.val) = 8 ∧
    (golayEncodedMask d.val).testBit 0 = false ∧
    (golayEncodedMask d.val).testBit 1 = false

/-- Actual encoded octad words containing both coordinates of the fixed root. -/
def generatedFeasibleOctadsContainingRootPair : Finset (Fin 4096) :=
  Finset.univ.filter fun d => golayMaskWeight (golayEncodedMask d.val) = 8 ∧
    (golayEncodedMask d.val).testBit 0 = true ∧
    (golayEncodedMask d.val).testBit 1 = true

set_option maxHeartbeats 8000000 in
-- Count the 4,096 original encoded Golay words using their actual physical support bits.
set_option maxRecDepth 10000 in
/-- Exactly 330 actual octads omit the fixed root pair. -/
theorem generatedFeasibleOctadsOutsideRootPair_card :
    generatedFeasibleOctadsOutsideRootPair.card = 330 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Count the same original codeword catalogue with both root coordinates present.
set_option maxRecDepth 10000 in
/-- Exactly 77 actual octads contain the fixed root pair. -/
theorem generatedFeasibleOctadsContainingRootPair_card :
    generatedFeasibleOctadsContainingRootPair.card = 77 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check all distinct local coordinate pairs against the 64 original even sign patterns.
set_option maxRecDepth 10000 in
/-- Every two distinct octad positions have equal signs in exactly 32 canonical patterns. -/
theorem generatedFeasibleOctadEqualSigns_card :
    ∀ i j : Fin 8, i ≠ j →
      (Finset.univ.filter fun e : Fin 64 =>
        (trialityEvenMask e).testBit i.val = (trialityEvenMask e).testBit j.val).card = 32 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

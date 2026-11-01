/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortMatching
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortPackedChecks

/-! Constructive finite short-coordinate matching with certified intrinsic target coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- A compact target evaluator still checks every original binary and central coordinate. -/
def generatedFourthMonomialShortMatchPacked (k : Fin 4) (q : Q) (n : ℤ) (w : ℕ) : Prop :=
  n ≠ 0 → generatedFourthLiftShortTargetValid w ∧
    toAdd (generatedFourthMonomialCorrectedQImage k q).base =
      toAdd (generatedFourthLiftShortTargetQPacked w).base ∧
    toAdd (generatedFourthMonomialCorrectedQImage k q).coeff =
      generatedFourthLiftShortTargetPhase w ∧
    generatedFourthLiftShortTargetNumerator w =
      (if generatedFourthLiftShortTargetPhase w = 0 then 1 else -1) * n

instance (k : Fin 4) (q : Q) (n : ℤ) (w : ℕ) :
    Decidable (generatedFourthMonomialShortMatchPacked k q n w) :=
  inferInstanceAs (Decidable (n ≠ 0 → generatedFourthLiftShortTargetValid w ∧
    toAdd (generatedFourthMonomialCorrectedQImage k q).base =
      toAdd (generatedFourthLiftShortTargetQPacked w).base ∧
    toAdd (generatedFourthMonomialCorrectedQImage k q).coeff =
      generatedFourthLiftShortTargetPhase w ∧
    generatedFourthLiftShortTargetNumerator w =
      (if generatedFourthLiftShortTargetPhase w = 0 then 1 else -1) * n))

/-- Packing changes only evaluation, preserving the exact full-Q and signed-coordinate meaning. -/
theorem generatedFourth_monomial_short_match_packed (k : Fin 4) (q : Q) (n : ℤ) (w : ℕ) :
    generatedFourthMonomialShortMatch k q n w ↔
      generatedFourthMonomialShortMatchPacked k q n w := by
  simp only [generatedFourthMonomialShortMatch, generatedFourthMonomialShortMatchPacked,
    generatedFourth_lift_short_target_q_packed]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

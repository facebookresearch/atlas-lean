/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortFiniteData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortThetaCache

/-! Faster certificate evaluation using proved original theta values. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- Original target Q evaluation with every theta coefficient already certified. -/
def generatedFourthLiftShortTargetQFast (w : ℕ) : Q :=
  if generatedFourthLiftShortTargetKind w then
    generatedFourthLiftShortOctadQFast (generatedFourthLiftShortTargetOctad w)
      (generatedFourthLiftShortTargetSign w)
  else generatedFourthLiftShortPairQ (generatedFourthLiftShortTargetPairSign w)
    (generatedFourthLiftShortTargetFirst w) (generatedFourthLiftShortTargetSecond w)

/-- Faster evaluation is exactly the original preferred target evaluator. -/
theorem generatedFourth_lift_short_target_q_fast (w : ℕ) :
    generatedFourthLiftShortTargetQ w = generatedFourthLiftShortTargetQFast w := by
  simp only [generatedFourthLiftShortTargetQ, generatedFourthLiftShortTargetQFast,
    generatedFourth_lift_short_octad_q_fast]

/-- The unchanged original certificate with certified theta evaluation. -/
def generatedFourthLiftShortFiniteMatchFast (q : Q) (n : ℤ) (w : ℕ) : Prop :=
  n ≠ 0 → generatedFourthLiftShortTargetValid w ∧
    toAdd (generatedFourthLiftShortMatrixFast q).base =
      toAdd (generatedFourthLiftShortTargetQFast w).base ∧
    toAdd (generatedFourthLiftShortMatrixFast q).coeff = generatedFourthLiftShortTargetPhase w ∧
    generatedFourthLiftShortTargetNumerator w =
      (if generatedFourthLiftShortTargetPhase w = 0 then 1 else -1) * n

instance (q : Q) (n : ℤ) (w : ℕ) : Decidable (generatedFourthLiftShortFiniteMatchFast q n w) :=
  inferInstanceAs (Decidable (n ≠ 0 → generatedFourthLiftShortTargetValid w ∧
    toAdd (generatedFourthLiftShortMatrixFast q).base =
      toAdd (generatedFourthLiftShortTargetQFast w).base ∧
    toAdd (generatedFourthLiftShortMatrixFast q).coeff = generatedFourthLiftShortTargetPhase w ∧
    generatedFourthLiftShortTargetNumerator w =
      (if generatedFourthLiftShortTargetPhase w = 0 then 1 else -1) * n))

/-- Faster matching has exactly the full actual-Q and original-coefficient certificate meaning. -/
theorem generatedFourth_lift_short_finite_match_fast (q : Q) (n : ℤ) (w : ℕ) :
    generatedFourthLiftShortFiniteMatch q n w ↔ generatedFourthLiftShortFiniteMatchFast q n w := by
  simp only [generatedFourthLiftShortFiniteMatch, generatedFourthLiftShortFiniteMatchFast,
    generatedFourth_lift_short_target_q_fast]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

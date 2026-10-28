/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortFiniteData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortBinaryAssembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortBinaryLinear

/-! Packed evaluation of the unchanged original full-Q and short-coefficient certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- Target evaluation with certified packed intrinsic preferred-Q coordinates. -/
def generatedFourthLiftShortTargetQPacked (w : ℕ) : Q :=
  if generatedFourthLiftShortTargetKind w then
    generatedFourthLiftShortOctadQPacked (generatedFourthLiftShortTargetOctad w)
      (generatedFourthLiftShortTargetSign w)
  else generatedFourthLiftShortPairQ (generatedFourthLiftShortTargetPairSign w)
    (generatedFourthLiftShortTargetFirst w) (generatedFourthLiftShortTargetSecond w)

/-- Packed target evaluation retains the genuine original preferred lift. -/
theorem generatedFourth_lift_short_target_q_packed (w : ℕ) :
    generatedFourthLiftShortTargetQ w = generatedFourthLiftShortTargetQPacked w := by
  simp only [generatedFourthLiftShortTargetQ, generatedFourthLiftShortTargetQPacked,
    generatedFourth_lift_short_octad_q_packed]

/-- The original full-Q evaluator equals the certified sparse binary and central evaluator. -/
theorem generatedFourth_lift_short_matrix_fast_sparse (q : Q) :
    generatedFourthLiftShortMatrixFast q = generatedFourthLiftShortMatrixSparse q :=
  (generatedFourth_lift_short_matrix_fast q).symm.trans
    (generatedFourth_lift_short_matrix_sparse q)

/-- The full original certificate evaluated with certified packed target coordinates. -/
def generatedFourthLiftShortFiniteMatchPacked (q : Q) (n : ℤ) (w : ℕ) : Prop :=
  n ≠ 0 → generatedFourthLiftShortTargetValid w ∧
    toAdd (generatedFourthLiftShortMatrixSparse q).base =
      toAdd (generatedFourthLiftShortTargetQPacked w).base ∧
    toAdd (generatedFourthLiftShortMatrixSparse q).coeff = generatedFourthLiftShortTargetPhase w ∧
    generatedFourthLiftShortTargetNumerator w =
      (if generatedFourthLiftShortTargetPhase w = 0 then 1 else -1) * n

instance (q : Q) (n : ℤ) (w : ℕ) : Decidable (generatedFourthLiftShortFiniteMatchPacked q n w) :=
  inferInstanceAs (Decidable (n ≠ 0 → generatedFourthLiftShortTargetValid w ∧
    toAdd (generatedFourthLiftShortMatrixSparse q).base =
      toAdd (generatedFourthLiftShortTargetQPacked w).base ∧
    toAdd (generatedFourthLiftShortMatrixSparse q).coeff = generatedFourthLiftShortTargetPhase w ∧
    generatedFourthLiftShortTargetNumerator w =
      (if generatedFourthLiftShortTargetPhase w = 0 then 1 else -1) * n))

/-- Packed matching has exactly the original full-Q and original-coordinate certificate meaning. -/
theorem generatedFourth_lift_short_finite_match_packed (q : Q) (n : ℤ) (w : ℕ) :
    generatedFourthLiftShortFiniteMatch q n w ↔
      generatedFourthLiftShortFiniteMatchPacked q n w := by
  simp only [generatedFourthLiftShortFiniteMatch, generatedFourthLiftShortFiniteMatchPacked,
    generatedFourth_lift_short_target_q_packed, generatedFourth_lift_short_matrix_fast_sparse]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

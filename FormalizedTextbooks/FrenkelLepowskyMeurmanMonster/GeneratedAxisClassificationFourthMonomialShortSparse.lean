/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialQMatrixSparse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortPacked

/-! Finite full-phase short matching evaluated with the certified sparse original Q action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- Exact finite intrinsic-Q and original-coefficient conditions, using the sparse evaluator. -/
def generatedFourthMonomialShortMatchSparse (k : Fin 4) (q : Q) (n : ℤ) (w : ℕ) : Prop :=
  n ≠ 0 → generatedFourthLiftShortTargetValid w ∧
    toAdd (generatedFourthMonomialQMatrixSparse k q).base =
      toAdd (generatedFourthLiftShortTargetQPacked w).base ∧
    toAdd (generatedFourthMonomialQMatrixSparse k q).coeff =
      generatedFourthLiftShortTargetPhase w ∧
    generatedFourthLiftShortTargetNumerator w =
      (if generatedFourthLiftShortTargetPhase w = 0 then 1 else -1) * n

instance (k : Fin 4) (q : Q) (n : ℤ) (w : ℕ) :
    Decidable (generatedFourthMonomialShortMatchSparse k q n w) :=
  inferInstanceAs (Decidable (n ≠ 0 → generatedFourthLiftShortTargetValid w ∧
    toAdd (generatedFourthMonomialQMatrixSparse k q).base =
      toAdd (generatedFourthLiftShortTargetQPacked w).base ∧
    toAdd (generatedFourthMonomialQMatrixSparse k q).coeff =
      generatedFourthLiftShortTargetPhase w ∧
    generatedFourthLiftShortTargetNumerator w =
      (if generatedFourthLiftShortTargetPhase w = 0 then 1 else -1) * n))

/-- Sparse checks have exactly the genuine full-Q and original signed-coordinate meaning. -/
theorem generatedFourth_monomial_short_match_sparse (k : Fin 4) (q : Q) (n : ℤ) (w : ℕ) :
    generatedFourthMonomialShortMatch k q n w ↔
      generatedFourthMonomialShortMatchSparse k q n w := by
  rw [generatedFourth_monomial_short_match_packed]
  simp only [generatedFourthMonomialShortMatchPacked, generatedFourthMonomialShortMatchSparse,
    generatedFourth_monomial_q_image_sparse]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

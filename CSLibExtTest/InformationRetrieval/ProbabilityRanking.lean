/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.InformationRetrieval.ProbabilityRanking
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Tests for the probability ranking principle
-/

set_option autoImplicit false

open Cslib.InformationRetrieval

namespace CSLibExtTest.InformationRetrieval.ProbabilityRanking

/-- The zero law has zero marginals. -/
example {N : ℕ} (i : Fin N) : relevanceMarginal (fun _ => 0) i = 0 := by
  simp [relevanceMarginal]

/-- The zero law has zero expected precision. -/
example {N k : ℕ} (r : Fin k → Fin N) :
    expectedPrecisionAt (fun _ => 0) r = 0 := by
  simp [expectedPrecisionAt]

/-- Expected precision at the empty cutoff is zero for every joint law. -/
example {N : ℕ} (μ : (Fin N → Bool) → ℝ) (r : Fin 0 → Fin N) :
    expectedPrecisionAt μ r = 0 := by
  simp [expectedPrecisionAt, precisionAt]

/-- The marginal-average identity, as an example. -/
example {N k : ℕ} (μ : (Fin N → Bool) → ℝ) (r : Fin k → Fin N) (hk : k ≠ 0) :
    expectedPrecisionAt μ r =
      (∑ j, relevanceMarginal μ (r j)) / (k : ℝ) :=
  expectedPrecisionAt_eq_average_marginals μ r hk

/-- At cutoff two, the identity is the average of the two selected marginals. -/
example {N : ℕ} (μ : (Fin N → Bool) → ℝ) (a b : Fin N) :
    expectedPrecisionAt μ ![a, b] =
      (relevanceMarginal μ a + relevanceMarginal μ b) / 2 := by
  rw [expectedPrecisionAt_eq_average_marginals μ ![a, b] (by norm_num),
    Fin.sum_univ_two]
  norm_num

/-- An optimal marginal-sorted prefix exists, as an example. -/
example {N k : ℕ} (hk : k ≤ N) (μ : (Fin N → Bool) → ℝ)
    (hμ : ∀ rel, 0 ≤ μ rel) :
    ∃ s : {s : Equiv.Perm (Fin N) // Antitone (relevanceMarginal μ ∘ s)},
      ∀ r : Fin k → Fin N, Function.Injective r →
        expectedPrecisionAt μ r ≤
          expectedPrecisionAt μ (fun i => s.1 (Fin.castLE hk i)) :=
  exists_sorted_expectedPrecisionAt hk hμ

end CSLibExtTest.InformationRetrieval.ProbabilityRanking

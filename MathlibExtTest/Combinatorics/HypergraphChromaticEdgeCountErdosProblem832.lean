/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.HypergraphChromaticEdgeCountErdosProblem832
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.NormNum

/-! # Regressions for the refutation of Erdős Problem 832 -/

namespace MathlibExtTest.HypergraphChromaticEdgeCountErdosProblem832

open MathlibExt.Combinatorics.HypergraphChromaticEdgeCountErdosProblem832Wanted
open MathlibExt.Combinatorics.HypergraphColoringShared

-- Extract counterexamples beyond every threshold, retaining exact chromatic number and the
-- equality clause. This uses only the public statement and works with either way to refute it.
example : ∃ r : ℕ, 3 ≤ r ∧ ∀ K : ℕ, ∃ k ≥ K,
    ∃ (n : ℕ) (H : Finset (Finset (Fin n))),
      (∀ e ∈ H, e.card = r) ∧ HypergraphColorable H k ∧ ¬ HypergraphColorable H (k - 1) ∧
        ¬ (((r - 1) * (k - 1) + 1).choose r ≤ H.card ∧
          (H.card = ((r - 1) * (k - 1) + 1).choose r →
            ∃ S : Finset (Fin n), S.card = (r - 1) * (k - 1) + 1 ∧ H = S.powersetCard r)) := by
  classical
  simpa only [chromaticEdgeLowerBound, Filter.eventually_atTop, not_forall, not_exists, not_imp,
    not_not, exists_prop] using chromaticEdgeLowerBound_refuted

-- At the first value used in the construction, the scaled tuple estimate is already strictly
-- below the scaled binomial benchmark. No enumeration of vertices, edges, or colorings is needed.
example : (15 * 1300 + 3 : ℕ) ^ 15 + 9 * (10 * 1300 + 2) ^ 15 <
    3 * (Nat.factorial 15 * (14 * 1300 + 1).choose 15) := by
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  exact lt_of_lt_of_le (b := 3 * (14 * 1300 - 13 : ℕ) ^ 15) (by norm_num)
    (Nat.mul_le_mul_left 3 (Nat.pow_sub_le_descFactorial (14 * 1300 + 1) 15))

end MathlibExtTest.HypergraphChromaticEdgeCountErdosProblem832

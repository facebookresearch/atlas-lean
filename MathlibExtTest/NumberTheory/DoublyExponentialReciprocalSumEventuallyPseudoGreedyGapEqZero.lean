/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DoublyExponentialReciprocalSumEventuallyPseudoGreedyGapEqZero
import Mathlib.Tactic.NormNum

/-!
# Tests for eventual vanishing of rational pseudo-greedy gaps

Eventual nonnegativity of the gaps of a positive rational implies that its expansion
eventually satisfies the Sylvester recurrence.

Reference: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28 (arXiv:2504.05933), Proposition 1 and Lemma 2.
-/

open Filter MetaMathlibExt

namespace MathlibExtTest.NumberTheory.DoublyExponentialReciprocalSumEventuallyPseudoGreedyGapEqZero

example {r : ℚ} (hr : 0 < r) (h : ∀ᶠ n in atTop, 0 ≤ pseudoGreedyGap r n) :
    ∀ᶠ n in atTop, pseudoGreedyExpansion r (n + 1) =
      pseudoGreedyExpansion r n ^ 2 - pseudoGreedyExpansion r n + 1 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_pseudoGreedyGap_eq_zero hr (Or.inr h))
  refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  have hrec := pseudoGreedyExpansion_succ_eq (r := (r : ℝ)) (by exact_mod_cast hr) n
  rw [hN n hn, hN (n + 1) (by omega)] at hrec
  norm_num at hrec
  exact_mod_cast hrec

end MathlibExtTest.NumberTheory.DoublyExponentialReciprocalSumEventuallyPseudoGreedyGapEqZero

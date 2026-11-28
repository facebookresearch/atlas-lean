/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.Bernoulli.StirlingInversion

open MathlibExt.NumberTheory.BernoulliSecondKindWanted MetaMathlibExt

-- The second-kind transform retains the constant term and adds the two positive-degree terms.
example (u v : ℕ → ℚ)
    (h : ∀ n, u n = ∑ k ∈ Finset.range (n + 1), (signedStirlingFirst n k : ℚ) * v k) :
    v 0 = u 0 ∧ v 2 = u 1 + u 2 := by
  have hv := (stirling_inversion_iff u v).mp h
  refine ⟨by simpa using hv 0, ?_⟩
  simpa [Finset.sum_range_succ, Nat.stirlingSecond] using hv 2

-- The inverse also retains the constant term, but the off-diagonal coefficient is negative.
example (u v : ℕ → ℚ)
    (h : ∀ n, v n = ∑ k ∈ Finset.range (n + 1), (Nat.stirlingSecond n k : ℚ) * u k) :
    u 0 = v 0 ∧ u 2 = v 2 - v 1 := by
  have hu := (stirling_inversion_iff u v).mpr h
  refine ⟨by simpa using hu 0, ?_⟩
  rw [hu 2]
  norm_num [Finset.sum_range_succ, signedStirlingFirst_apply, Nat.stirlingFirst,
    sub_eq_add_neg, add_comm]

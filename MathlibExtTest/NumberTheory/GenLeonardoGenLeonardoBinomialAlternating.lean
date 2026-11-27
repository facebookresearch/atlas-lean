/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GenLeonardoGenLeonardoBinomialAlternating

/-! # Tests for alternating binomial identities for generalized Leonardo numbers -/

namespace MathlibExtTest.NumberTheory.GenLeonardoGenLeonardoBinomialAlternating

open Finset MetaMathlibExt

-- At `k = 1`, `n = 2`, `r = 0`: `1 - 6 + 9 = 4`.
example : (∑ i ∈ range (2 + 1), (Nat.choose 2 i : ℤ) * (-1 : ℤ) ^ (2 - i) *
    genLeonardo 1 (2 * i + 0)) = 4 := by
  have h := (genLeonardo_binomial_alternating (1 : ℤ) 2 0 (by decide)).1
  have hR : genLeonardo (1 : ℤ) (2 + 0) + 1 = 4 := rfl
  rw [hR] at h
  exact h

-- At `k = 1`, `n = 2`, `r = 0`: `0 - 12 + 20 = 8`.
example : (∑ i ∈ range (2 + 1), (Nat.choose 2 i : ℤ) * (-1 : ℤ) ^ (2 - i) *
    genLeonardoCompanion 1 (2 * i + 0)) = 8 := by
  have h := (genLeonardo_binomial_alternating (1 : ℤ) 2 0 (by decide)).2
  have hR : genLeonardoCompanion (1 : ℤ) (2 + 0) + 2 * 1 = 8 := rfl
  rw [hR] at h
  exact h

end MathlibExtTest.NumberTheory.GenLeonardoGenLeonardoBinomialAlternating

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LexMinimalExtensionPeriod

open MetaMathlibExt

-- A one-entry prefix of the zero sequence attains its maximum only at length one.
example : (maxAverageIndices (0 : ℕ → ℕ) 1).gcd id ∣ 1 := by
  refine (isLexMinimalExtensionOf_zero 1).gcd_maxAverageIndices_dvd_minimalPeriod le_rfl ?_
  exact ⟨⟨Nat.one_pos, 0, fun _ _ => rfl⟩, fun _ hq => hq.1⟩

-- For the prefix `0, 2`, the sole maximizing length is two, so the least period is even.
example {η : ℕ → ℕ} {p : ℕ} (hη : IsLexMinimalExtensionOf η 2) (h₀ : η 0 = 0) (h₁ : η 1 = 2)
    (hp : IsLeast {q : ℕ | 0 < q ∧ ∃ N, ∀ i, N ≤ i → η (i + q) = η i} p) : 2 ∣ p := by
  have h₂ : binomidAverage η 2 = 1 := by
    norm_num [binomidAverage, Finset.sum_range_succ, h₀, h₁]
  have hI : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  have hJ : maxAverageIndices η 2 = {2} := by
    norm_num [maxAverageIndices, hI, Finset.filter_insert, Finset.filter_singleton,
      binomidAverage_one, h₀, h₂]
  simpa [hJ] using hη.gcd_maxAverageIndices_dvd_minimalPeriod (by decide) hp

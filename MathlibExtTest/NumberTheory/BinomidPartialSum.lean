/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BinomidPartialSum

open MetaMathlibExt

/-- There is no split at length one, so an empty initial prefix forces the first entry to zero. -/
example {η : ℕ → ℕ} (hη : IsLexMinimalExtensionOf η 0) : η 0 = 0 := by
  simpa using (isBinomidIndex_iff_partialSum η).2 0 hη 1 (by decide)

/-- After the prefix (0, 3), the split 2 + 2 gives the unique maximum at length four. -/
example {η : ℕ → ℕ} (hη : IsLexMinimalExtensionOf η 2) (h₀ : η 0 = 0) (h₁ : η 1 = 3) :
    η 2 = 0 ∧ η 3 = 3 := by
  have h := (isBinomidIndex_iff_partialSum η).2 2 hη
  have hthree := h 3 (by decide)
  have hfour := h 4 (by decide)
  have h₂ : η 2 = 0 := by
    simpa [show Finset.Ico 1 3 = {1, 2} by decide, Finset.sum_range_succ, h₀, h₁] using hthree
  refine ⟨h₂, ?_⟩
  simp [show Finset.Ico 1 4 = {1, 2, 3} by decide, Finset.sum_range_succ, h₀, h₁, h₂] at hfour
  omega

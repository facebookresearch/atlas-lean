/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LexMinimalExtensionMonoidBinomidAverageLe
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.NumberTheory.LexMinimalExtensionMonoidBinomidAverageLe` -/

namespace MathlibExtTest.NumberTheory.LexMinimalExtensionMonoidBinomidAverageLe

open MetaMathlibExt

/-- A lex-minimal extension of one entry never exceeds that entry on average. -/
example {η : ℕ → ℕ} (hη : IsLexMinimalExtensionOf η 1) {i : ℕ} (hi : 1 ≤ i) :
    binomidAverage η i ≤ η 0 := by
  have h := hη.binomidAverage_le (i := i) hi (j := 1) (by simp [maxAverageIndices_one])
  rwa [binomidAverage_one] at h

/-- For the prefix `0, 2`, every average of a lex-minimal extension is at most one. -/
example {η : ℕ → ℕ} (hη : IsLexMinimalExtensionOf η 2) (h₀ : η 0 = 0) (h₁ : η 1 = 2)
    {i : ℕ} (hi : 1 ≤ i) : binomidAverage η i ≤ 1 := by
  have h₂ : binomidAverage η 2 = 1 := by
    norm_num [binomidAverage, Finset.sum_range_succ, h₀, h₁]
  have hJ : maxAverageIndices η 2 = {2} := by
    have hI : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
    norm_num [maxAverageIndices, hI, Finset.filter_insert, Finset.filter_singleton,
      binomidAverage_one, h₀, h₂]
  have h := hη.binomidAverage_le (i := i) hi (j := 2) (by simp [hJ])
  rwa [h₂] at h

/-- Any two maximal-prefix averages of a lex-minimal extension are equal. -/
example {η : ℕ → ℕ} {m : ℕ} (hη : IsLexMinimalExtensionOf η m) {j₁ j₂ : ℕ}
    (h₁ : j₁ ∈ maxAverageIndices η m) (h₂ : j₂ ∈ maxAverageIndices η m) :
    binomidAverage η j₁ = binomidAverage η j₂ := by
  have mem (k : ℕ) (hk : k ∈ maxAverageIndices η m) : 1 ≤ k := by
    simp only [maxAverageIndices, Finset.mem_filter] at hk
    exact (Finset.mem_Icc.mp hk.1).1
  exact le_antisymm (hη.binomidAverage_le (mem j₁ h₁) h₂)
    (hη.binomidAverage_le (mem j₂ h₂) h₁)

end MathlibExtTest.NumberTheory.LexMinimalExtensionMonoidBinomidAverageLe

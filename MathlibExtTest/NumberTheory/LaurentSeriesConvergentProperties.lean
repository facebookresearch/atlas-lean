/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LaurentSeriesConvergentProperties

open MetaMathlibExt

variable {K : Type*} [Field K] (α : LaurentSeries K) (hα : LaurentIsIrrational α)

-- At the first nontrivial convergent there is exactly one inner tail to check.
example (β : LaurentSeries K) (hβ : β ≠ 0) (ht : laurentPartialQuotient α 1 + β⁻¹ ≠ 0) :
    (β * laurentConvNum α 2 + laurentPartialQuotient α 0) /
        (β * laurentPartialQuotient α 1 + 1) =
      laurentPartialQuotient α 0 + (laurentPartialQuotient α 1 + β⁻¹)⁻¹ := by
  have h := (laurentConvergent_properties α hα).1 1 β hβ (by
    intro k hk hk'
    obtain rfl : k = 1 := by omega
    exact ht)
  rw [show List.range (1 + 1) = [0, 1] by decide] at h
  simpa [laurentConvNum, laurentConvDen] using h

-- When the polynomial part vanishes, the first nontrivial convergent is the reciprocal of b₁.
example (h₀ : laurentPartialQuotient α 0 = 0) :
    (α - (laurentPartialQuotient α 1)⁻¹).order =
      -(laurentPartialQuotient α 2).order - 2 * (laurentPartialQuotient α 1).order := by
  simpa [laurentConvNum, laurentConvDen, h₀] using
    (laurentConvergent_properties α hα).2.2.2.2.1 1 le_rfl

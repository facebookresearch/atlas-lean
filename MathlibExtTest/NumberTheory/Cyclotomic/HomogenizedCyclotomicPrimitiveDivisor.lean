/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.IntervalCases
import MathlibExt.NumberTheory.Cyclotomic.HomogenizedCyclotomicPrimitiveDivisor

/-! # Tests for primitive prime divisors of homogenized cyclotomic values -/

open MetaMathlibExt

-- At the composite index four, five divides none of the earlier positive-indexed terms.
example : (5 : ℤ) ∣ homogenizedCyclotomic 4 2 1 := by
  refine dvd_homogenizedCyclotomic_of_isPrimitivePrimeDivisor (a := 2) (b := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) ?_
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro s hs hs4
  interval_cases s <;> decide

-- The least allowed exponent also works with the smaller base first.
example : (3 : ℤ) ∣ homogenizedCyclotomic 2 1 2 := by
  refine dvd_homogenizedCyclotomic_of_isPrimitivePrimeDivisor (a := 1) (b := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) ?_
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro s hs hs2
  interval_cases s
  decide

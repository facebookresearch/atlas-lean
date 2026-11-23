/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.AbsoluteLucasPseudoprimes

open MetaMathlibExt

-- With signs (-1, 1, -1), transfer all three divisibilities from 2 to -4 modulo 6.
example : ∀ c ∈ ({1, 2, 3} : Finset ℤ), c * (-4) ∣ -456 := by
  apply mul_dvd_prod_sub_sign_of_modEq (ε₁ := -1) (ε₂ := 1) (ε₃ := -1)
    (g := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    isCoprime_one_left isCoprime_one_left ⟨-1, 1, by decide⟩ (by decide) _ (by decide) (by decide)
  intro c hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl <;> decide

-- At g = 1 with all signs positive, even the second divisibility fails.
example : ¬ (2 : ℤ) ∣ (1 + 1) * (2 + 1) * (3 + 1) - 1 := by decide

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModifiedDegenerateBernoulli

open MetaMathlibExt

-- Degree zero uses the inverse of the scaling factor, including at the singular parameters.
example (lam x : ℂ) :
    modifiedDegenerateBernoulli lam 0 x = lam / Complex.log (1 + lam) := by
  simp [modifiedDegenerateBernoulli]

-- At degree two the scaling factor occurs exactly once.
example (lam : ℂ) :
    modifiedDegenerateBernoulli lam 2 0 = Complex.log (1 + lam) / lam / 6 := by
  norm_num [modifiedDegenerateBernoulli, Polynomial.aeval_def, Polynomial.eval₂_at_zero,
    Polynomial.coeff_bernoulli, bernoulli_two, div_eq_mul_inv]

-- At the smallest admissible degree each convolution has just its middle term.
example (lam : ℂ) (h₀ : lam ≠ 0) (h₁ : lam ≠ -1) :
    6 * modifiedDegenerateBernoulli lam 2 0 ^ 2 +
      5 * (lam / Complex.log (1 + lam)) * modifiedDegenerateBernoulli lam 4 0 = 0 := by
  have h := modifiedDegenerateBernoulli_matiyasevich 4 (by decide) lam h₀ h₁
  norm_num [Nat.choose] at h
  linear_combination -h / 4

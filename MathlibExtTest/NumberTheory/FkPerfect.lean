/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FkPerfect

namespace MathlibExtTest.NumberTheory.FkPerfect

open MathlibExt.NumberTheory.FkPerfectWanted

-- `15 = 3 * 5` is not deficient `F₂`-perfect.
example : ¬ IsDeficientFkPerfect 2 15 := by
  have h15 : ∏ p ∈ ({3, 5} : Finset ℕ), p = 15 := by decide
  rw [← h15]
  exact not_isDeficientFkPerfect_prod_primes 2 (by decide) {3, 5} (by decide)

-- `105 = 3 * 5 * 7` is not deficient `F₃`-perfect.
example : ¬ IsDeficientFkPerfect 3 105 := by
  have h105 : ∏ p ∈ ({3, 5, 7} : Finset ℕ), p = 105 := by decide
  rw [← h105]
  exact not_isDeficientFkPerfect_prod_primes 3 (by decide) {3, 5, 7} (by decide)

end MathlibExtTest.NumberTheory.FkPerfect

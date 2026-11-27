/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.SuperMZumkellerIsSuperMZumkellerProdPrimes

namespace MathlibExtTest.NumberTheory.SuperMZumkellerIsSuperMZumkellerProdPrimes

open MathlibExt.NumberTheory.SuperMZumkellerWanted

-- The product 2 * 3 * 5 = 30 is super-m-Zumkeller.
example : IsSuperMZumkeller 30 := by
  have h30 : (∏ p ∈ ({2, 3, 5} : Finset ℕ), p) = 30 := by decide
  rw [← h30]
  exact isSuperMZumkeller_prod_primes _ (by decide) (by decide)

-- The product 2 * 3 * 5 * 7 = 210 is super-m-Zumkeller.
example : IsSuperMZumkeller 210 := by
  have h210 : (∏ p ∈ ({2, 3, 5, 7} : Finset ℕ), p) = 210 := by decide
  rw [← h210]
  exact isSuperMZumkeller_prod_primes _ (by decide) (by decide)

end MathlibExtTest.NumberTheory.SuperMZumkellerIsSuperMZumkellerProdPrimes

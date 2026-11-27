/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FkPerfectSquarefreeOdd

/-! # Tests for the near Fₖ-perfect exclusion for products of distinct odd primes -/

namespace MathlibExtTest.NumberTheory.FkPerfectSquarefreeOdd

open MathlibExt.NumberTheory.FkPerfectWanted

-- The empty prime set gives 1, which has no proper divisors.
example : ¬ IsNearFkPerfect 2 1 := by
  simpa only [Finset.prod_empty] using
    not_isNearFkPerfect_prod_primes 2 (by decide) ∅ (by simp)

-- The parity argument also applies to a singleton set.
example : ¬ IsNearFkPerfect 2 3 := by
  simpa only [Finset.prod_singleton] using
    not_isNearFkPerfect_prod_primes 2 (by decide) {3} (by
      intro p hp
      simp only [Finset.mem_singleton] at hp
      subst p
      decide)

-- A composite squarefree input, with an odd exponent.
example : ¬ IsNearFkPerfect 3 15 := by
  change ¬ IsNearFkPerfect 3 (3 * 5)
  have h := not_isNearFkPerfect_prod_primes 3 (by decide) {3, 5} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> decide)
  simpa only [Finset.prod_insert (by decide : (3 : ℕ) ∉ ({5} : Finset ℕ)),
    Finset.prod_singleton] using h

end MathlibExtTest.NumberTheory.FkPerfectSquarefreeOdd

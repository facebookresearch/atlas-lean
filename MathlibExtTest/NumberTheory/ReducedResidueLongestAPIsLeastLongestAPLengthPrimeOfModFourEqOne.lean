/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ReducedResidueLongestAPIsLeastLongestAPLengthPrimeOfModFourEqOne

namespace MathlibExtTest.NumberTheory.ReducedResidueLongestAPIsLeastLongestAPLengthPrimeOfModFourEqOne

open MetaMathlibExt

-- At the smallest prime in this congruence class the minimum of two is attained.
example : ∃ m, longestAPLength m 5 = 2 := by
  obtain ⟨m, hm⟩ :=
    (isLeast_longestAPLength_prime_of_mod_four_eq_one (p := 5) (by decide) rfl).1
  refine ⟨m, ?_⟩
  simpa using hm

-- Every window modulo thirteen contains a progression of length six.
example (m : ℤ) : 6 ≤ longestAPLength m 13 := by
  have h := (isLeast_longestAPLength_prime_of_mod_four_eq_one (p := 13)
    (by decide) rfl).2 ⟨m, rfl⟩
  simpa using h

end MathlibExtTest.NumberTheory.ReducedResidueLongestAPIsLeastLongestAPLengthPrimeOfModFourEqOne

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ReducedResidueLongestAPIsLeastLongestAPLengthPrimePow

/-! # Tests for `MathlibExt.NumberTheory.ReducedResidueLongestAPIsLeastLongestAPLengthPrimePow` -/

namespace MathlibExtTest.NumberTheory.ReducedResidueLongestAPIsLeastLongestAPLengthPrimePow

open MetaMathlibExt

-- Modulo four the least longest-progression length is two, and it is attained.
example : (2 : ℕ) ∈ Set.range (fun m : ℤ => longestAPLength m 4) := by
  simpa using
    (isLeast_longestAPLength_prime_pow (p := 2) (r := 2) (by decide) (by decide)).1

-- Every window modulo nine contains an arithmetic progression of length three.
example (m : ℤ) : 3 ≤ longestAPLength m 9 := by
  have h := (isLeast_longestAPLength_prime_pow (p := 3) (r := 2) (by decide) (by decide)).2
  simpa using h ⟨m, rfl⟩

end MathlibExtTest.NumberTheory.ReducedResidueLongestAPIsLeastLongestAPLengthPrimePow

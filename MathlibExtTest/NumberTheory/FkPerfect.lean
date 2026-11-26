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

-- Eight is a prime power, so it is neither deficient `F`-perfect nor near `F`-perfect.
example : ¬ IsDeficientFPerfect 8 ∧ ¬ IsNearFPerfect 8 := by
  simpa using prime_pow_not_fPerfect 2 3 Nat.prime_two

-- Nine is a prime power, so it is not deficient `F`-perfect.
example : ¬ IsDeficientFPerfect 9 := by
  simpa using (prime_pow_not_fPerfect 3 2 (by decide)).1

-- Every prime is a prime power with exponent one.
example (p : ℕ) (hp : p.Prime) : ¬ IsDeficientFPerfect p ∧ ¬ IsNearFPerfect p := by
  simpa using prime_pow_not_fPerfect p 1 hp

end MathlibExtTest.NumberTheory.FkPerfect

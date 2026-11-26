/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryTriperfectNotFiveDvdOfFactorizationTwoEqFour
namespace MathlibExtTest.NumberTheory.ArithmeticFunction.BiunitaryTriperfect

example (N : ℕ) (hN : 0 < N) (hσ : MetaMathlibExt.sigmaBiunitary N = 3 * N)
    (he : N.factorization 2 = 4) (h5 : 5 ∣ N) : N.factorization 3 ≤ 4 := by
  exact Nat.le_of_lt_succ (lt_of_not_ge fun hf =>
    MetaMathlibExt.not_five_dvd_of_factorization_two_eq_four N hN hσ he hf h5)

end MathlibExtTest.NumberTheory.ArithmeticFunction.BiunitaryTriperfect

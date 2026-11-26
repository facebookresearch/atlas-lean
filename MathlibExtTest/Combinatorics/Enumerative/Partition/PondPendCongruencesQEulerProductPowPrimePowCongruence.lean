/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.PondPendCongruencesQEulerProductPowPrimePowCongruence

/-!
# Tests for the prime-power congruence for powers of Euler products

Concrete instances of `qEulerProduct_pow_prime_pow_congruence` at small primes.
-/

@[expose] public section

namespace MathlibExtTest.Combinatorics.Enumerative.Partition.PondPendCongruencesQEulerProductPowPrimePowCongruence

-- At `p = 2` and `j = k = m = 1`, the coefficients of `𝔣 1 ^ 2` agree with those of `𝔣 2`
-- modulo two.
example (n : ℕ) :
    PowerSeries.coeff n (MetaMathlibExt.qEulerProduct 1 ^ 2) ≡
      PowerSeries.coeff n (MetaMathlibExt.qEulerProduct 2) [ZMOD 2] := by
  have h := MetaMathlibExt.qEulerProduct_pow_prime_pow_congruence 2 1 1 1 Nat.prime_two
    (by decide) (by decide) (by decide) n
  simpa using h

-- At `p = 3`, `j = k = 1` and `m = 2`, the coefficient difference is divisible by three.
example (n : ℕ) :
    (3 : ℤ) ∣ PowerSeries.coeff n (MetaMathlibExt.qEulerProduct (3 * 2)) -
      PowerSeries.coeff n (MetaMathlibExt.qEulerProduct 2 ^ 3) := by
  have h := MetaMathlibExt.qEulerProduct_pow_prime_pow_congruence 3 1 1 2 (by decide)
    (by decide) (by decide) (by decide) n
  simpa using h.dvd

end MathlibExtTest.Combinatorics.Enumerative.Partition.PondPendCongruencesQEulerProductPowPrimePowCongruence

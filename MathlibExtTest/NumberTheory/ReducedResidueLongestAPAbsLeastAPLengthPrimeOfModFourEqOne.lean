/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ReducedResidueLongestAPAbsLeastAPLengthPrimeOfModFourEqOne

/-!
# Tests for absolute least progression lengths at primes congruent to one modulo four

The formula of Phothila, Thoket and Kanasri, *Length of the Longest Arithmetic Progressions
in a Certain Reduced Residue System*, is applied at the primes five and thirteen.
-/

namespace MathlibExtTest.NumberTheory.ReducedResidueLongestAPAbsLeastAPLengthPrimeOfModFourEqOne

open MetaMathlibExt

example : absLeastAPLength 5 = 2 :=
  absLeastAPLength_prime_of_mod_four_eq_one (by decide) (by decide)

example : absLeastAPLength 13 = 6 :=
  absLeastAPLength_prime_of_mod_four_eq_one (by decide) (by decide)

end MathlibExtTest.NumberTheory.ReducedResidueLongestAPAbsLeastAPLengthPrimeOfModFourEqOne

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSum

open MathlibExt.NumberTheory.PrimitiveNondeficientWanted MetaMathlibExt

namespace MathlibExtTest.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSum

-- Below the crossing threshold, the lifted product stays at most two.
example (q : ℕ) (hq : q.Prime) (hodd : Odd q)
    (h : abundancySup (ordCompl[2] (q + 1)) < 2) :
    abundancySup (q * ordCompl[2] (q + 1)) ≤ 2 := by
  by_contra hcon
  exact not_abundancySup_oddPart_succ_lt_two_and_two_lt q hq hodd
    ⟨h, not_le.mp hcon⟩

-- At `q = 3` the odd part of `q + 1` is `1`.
example : ordCompl[2] (3 + 1) = 1 := by
  have h : (3 : ℕ) + 1 = 2 ^ 2 := by decide
  rw [h, Nat.ordCompl_self_pow Nat.prime_two]

-- The crossing is impossible at the concrete prime `q = 3`.
example : ¬ (abundancySup (ordCompl[2] (3 + 1)) < 2 ∧
    2 < abundancySup (3 * ordCompl[2] (3 + 1))) :=
  not_abundancySup_oddPart_succ_lt_two_and_two_lt 3 (by decide) (by decide)

end MathlibExtTest.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSum

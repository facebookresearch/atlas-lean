/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSum

/-! # Tests for `MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSum` -/

namespace MathlibExtTest.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSum

open MetaMathlibExt

-- With exponent 5 the disjunct `e = 1` is impossible, so the fifth-power bound holds.
example (n q m : ℕ) (h : EulerianForm n q 5 m) : q ^ 5 < 2 * m ^ 2 := by
  simpa using eulerianForm_exponent_eq_one_or_pow_five_lt n q 5 m h

-- Corollary: an exponent different from 1 forces the fifth-power bound.
example (n q e m : ℕ) (h : EulerianForm n q e m) (he : e ≠ 1) : q ^ 5 < 2 * m ^ 2 := by
  simpa [he] using eulerianForm_exponent_eq_one_or_pow_five_lt n q e m h

end MathlibExtTest.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSum

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.DivisorSumDensity

namespace MathlibExt.NumberTheory.AmicableWanted

-- The smallest allowed modulus has no exceptions.
example : {n : ℕ | ¬ 1 ∣ ArithmeticFunction.sigma 1 n} = ∅ := by simp

-- For modulus two, the exceptions are exactly the odd divisor sums.
example : {n : ℕ | Odd (ArithmeticFunction.sigma 1 n)}.HasDensity 0 := by
  simpa only [← even_iff_two_dvd, Nat.not_even_iff_odd] using
    tendsto_density_not_dvd_sigma 2 (by decide)

-- For modulus six, a factor five to exponent one suffices, but five squared is an exception.
example : 6 ∣ ArithmeticFunction.sigma 1 35 ∧ ¬ 6 ∣ ArithmeticFunction.sigma 1 25 := by decide

end MathlibExt.NumberTheory.AmicableWanted

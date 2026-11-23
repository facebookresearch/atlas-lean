/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DivisibilityRuns

namespace MetaMathlibExt

-- At the first allowed index the two seeds can cancel.
example : Int.gcd (gibonacciNumber (-6) 6 2) (-6) = 6 :=
  int_gcd_gibonacciNumber_sub_two (-6) 6 2 (by decide)

example (n : ℕ) (hn : 2 ≤ n) :
    Int.gcd (gibonacciNumber (-12) 18 n) (gibonacciNumber (-12) 18 (n - 2)) = 6 :=
  int_gcd_gibonacciNumber_sub_two (-12) 18 n hn

example (n : ℕ) (hn : 2 ≤ n) :
    Int.gcd (gibonacciNumber 0 0 n) (gibonacciNumber 0 0 (n - 2)) = 0 :=
  int_gcd_gibonacciNumber_sub_two 0 0 n hn

-- A zero third term ends the run even when the corresponding Tribonacci term is zero.
example : IsDivRunUpTo 2 (-2) 4 (-4) 0 2 := by decide
example : ¬ IsDivRunUpTo 2 (-2) 4 (-4) 0 3 := by decide

example : divRunCount 0 0 = 0 := by decide

end MetaMathlibExt

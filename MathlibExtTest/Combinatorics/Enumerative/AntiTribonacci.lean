/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AntiTribonacci

open MetaMathlibExt

-- The extra index zero returns the three initial summands and their sum.
example : (antiTribonacciA 0, antiTribonacciB 0, antiTribonacciC 0, antiTribonacciD 0) =
    (1, 2, 3, 6) := rfl

-- In the second triple the mex skips 6 between the second and third summands.
example : antiTribonacciState 1 = ((4, 5, 7, 16), {1, 2, 3, 4, 5, 6, 7, 16}) := by
  decide +kernel

-- Both endpoints of the bound on the sum occur.
example : 10 * (3 : ℤ) - 3 - antiTribonacciD 3 = 0 ∧
    10 * (8 : ℤ) - 3 - antiTribonacciD 8 = 2 := by
  decide +kernel

-- The bounds determine the entire first triple in each interval of ten.
example (q : ℕ) : antiTribonacciA (3 * q + 1) = 10 * q + 1 ∧
    antiTribonacciB (3 * q + 1) = 10 * q + 2 ∧ antiTribonacciC (3 * q + 1) = 10 * q + 3 := by
  have h := kimberling_antiTribonacci (n := 3 * q + 1) (hn := by omega)
  omega

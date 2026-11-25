/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.FiniteEulerProductCongruence
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Polynomial

namespace MetaMathlibExt

-- At t = 1 the scaled product occurs to the first power, for every truncation length.
example (N r : ℕ) : (3 : ℤ) ∣
    ((∏ m ∈ Finset.Icc 1 N, ((1 : Polynomial ℤ) - X ^ (2 * m))) ^ 3 -
      ∏ m ∈ Finset.Icc 1 N, ((1 : Polynomial ℤ) - X ^ (6 * m))).coeff r := by
  simpa using finiteEulerProduct_primePower_congruence 2 1 3 N
    (by decide) (by decide) (by decide) r

-- For p = t = 2 one factor already gives the full congruence modulo four.
example (r : ℕ) : (4 : ℤ) ∣ (((1 : Polynomial ℤ) - X) ^ 4 - (1 - X ^ 2) ^ 2).coeff r := by
  simpa using finiteEulerProduct_primePower_congruence 1 2 2 1
    (by decide) (by decide) (by decide) r

-- In degree three, above the truncation length one, the modulus four is sharp.
example : (((1 : Polynomial ℤ) - X) ^ 4 - (1 - X ^ 2) ^ 2).coeff 3 = -4 := by
  have h : ((1 : Polynomial ℤ) - X) ^ 4 - (1 - X ^ 2) ^ 2 =
      C (-4) * X ^ 3 + C 8 * X ^ 2 - C 4 * X := by
    simp only [map_neg, map_ofNat]
    ring
  norm_num [h, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X]

end MetaMathlibExt

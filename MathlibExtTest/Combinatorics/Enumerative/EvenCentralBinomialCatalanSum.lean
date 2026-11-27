/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.TouchardCatalanIdentity

namespace MetaMathlibExt

open Finset

-- The zero case has one summand.
example : ∑ k ∈ range (0 / 2 + 1),
    ((0 : ℕ).choose (2 * k) : ℚ) / (k + 1) / 2 ^ (2 * k) * ((2 * k).choose k : ℚ) = 1 := by
  refine (sum_choose_even_centralBinom_div_succ 0).trans ?_
  norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]

-- For even n, the last term has 2 * k = n.
example : ∑ k ∈ range (4 / 2 + 1),
    ((4 : ℕ).choose (2 * k) : ℚ) / (k + 1) / 2 ^ (2 * k) * ((2 * k).choose k : ℚ) = 21 / 8 := by
  refine (sum_choose_even_centralBinom_div_succ 4).trans ?_
  norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]

-- For odd n, the last term has 2 * k = n - 1.
example : ∑ k ∈ range (5 / 2 + 1),
    ((5 : ℕ).choose (2 * k) : ℚ) / (k + 1) / 2 ^ (2 * k) * ((2 * k).choose k : ℚ) = 33 / 8 := by
  refine (sum_choose_even_centralBinom_div_succ 5).trans ?_
  norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]

end MetaMathlibExt

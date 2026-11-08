/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.RStirlingSecond

@[expose] public section

namespace MetaMathlibExt

/-- `{4 \brace 3}_2 = 5`. -/
example : rStirlingSecond 4 3 2 = 5 := by decide
/-- `{n+1 \brace m+1}_1 = {n+1 \brace m+1}`: `{5 \brace 3}_1 = 25`. -/
example : rStirlingSecond 5 3 1 = Nat.stirlingSecond 5 3 := by decide
example : rStirlingSecond 3 2 3 = 0 := rStirlingSecond_eq_zero (Or.inl (by decide))
example (n m : ℕ) : rStirlingSecond n m 0 = Nat.stirlingSecond n m := rStirlingSecond_zero_right n m
example (n r : ℕ) : rStirlingSecond (n + r) r r = r ^ n := rStirlingSecond_add_self n r

end MetaMathlibExt

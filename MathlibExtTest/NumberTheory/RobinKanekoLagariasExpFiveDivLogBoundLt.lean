/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RobinKanekoLagariasExpFiveDivLogBoundLt

namespace MathlibExtTest.NumberTheory.RobinKanekoLagariasExpFiveDivLogBoundLt

open Real

-- The bound at the smallest allowed index.
example : exp (5 / log (((((13042 : ℕ) : ℝ) + 1) *
    (log (((13042 : ℕ) : ℝ) + 1) + log (log (((13042 : ℕ) : ℝ) + 1)) - 1)))) < 1.525 :=
  MetaMathlibExt.exp_five_div_log_bound_lt 13042 le_rfl

-- A looser uniform bound derived from the sharp one.
example (k : ℕ) (hk : 13042 ≤ k) :
    exp (5 / log (((k : ℝ) + 1) *
      (log ((k : ℝ) + 1) + log (log ((k : ℝ) + 1)) - 1))) < 2 :=
  lt_trans (MetaMathlibExt.exp_five_div_log_bound_lt k hk) (by norm_num)

end MathlibExtTest.NumberTheory.RobinKanekoLagariasExpFiveDivLogBoundLt

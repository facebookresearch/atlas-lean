/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HyperLeonardoLogConvex

namespace MetaMathlibExt

-- At order one the index-one inequality is log-convex: `2 ^ 2 = 4 ≤ 1 * 5`.
example : hyperLeonardo 1 1 ^ 2 ≤ hyperLeonardo 1 0 * hyperLeonardo 1 2 :=
  hyperLeonardo_logConvex_logConcave_one.1

-- At order two it is log-concave: `1 * 8 ≤ 3 ^ 2`.
example : hyperLeonardo 2 0 * hyperLeonardo 2 2 ≤ hyperLeonardo 2 1 ^ 2 :=
  hyperLeonardo_logConvex_logConcave_one.2 2 le_rfl

-- The order-two values behind that inequality.
example : hyperLeonardo 2 0 = 1 ∧ hyperLeonardo 2 1 = 3 ∧ hyperLeonardo 2 2 = 8 := by
  simp [hyperLeonardo, Finset.sum_range_succ, genLeonardo]

end MetaMathlibExt

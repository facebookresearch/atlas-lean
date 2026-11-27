/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HyperLeonardoHyperLeonardoConvex

namespace MathlibExtTest.NumberTheory.HyperLeonardoHyperLeonardoConvex

open MetaMathlibExt

-- At order zero and index one the convexity inequality reads `2 * 1 ≤ 1 + 3`.
example : 2 * hyperLeonardo 0 1 ≤ hyperLeonardo 0 0 + hyperLeonardo 0 2 :=
  hyperLeonardo_convex 0 1 (by decide)

-- At order one and index two the convexity inequality reads `2 * 5 ≤ 2 + 10`.
example : 2 * hyperLeonardo 1 2 ≤ hyperLeonardo 1 1 + hyperLeonardo 1 3 :=
  hyperLeonardo_convex 1 2 (by decide)

-- Convexity says successive differences are monotone.
example (r n : ℕ) (hn : 1 ≤ n) : hyperLeonardo r n - hyperLeonardo r (n - 1) ≤
    hyperLeonardo r (n + 1) - hyperLeonardo r n := by
  have h := hyperLeonardo_convex r n hn
  omega

-- The first step includes the next ordinary Leonardo number, `Le₁ = 1`.
example : hyperLeonardo 1 1 = hyperLeonardo 1 0 + 1 :=
  hyperLeonardo_one_succ 0

-- At the next step, order one contributes `2` and order zero contributes `3`.
example : hyperLeonardo 1 2 = 5 := by
  rw [hyperLeonardo_one_succ]
  exact (congrArg (· + 3) hyperLeonardo_one_small.2.1)

end MathlibExtTest.NumberTheory.HyperLeonardoHyperLeonardoConvex

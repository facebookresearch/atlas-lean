/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Combinatorics.Enumerative.GeneralizedLeonardoLogBehavior
public import WantedExt.NumberTheory.GenLeonardoWanted
public import MathlibExt.Combinatorics.Enumerative.GeneralizedLeonardoLogBehaviorGenLeonardoPowSelfLogConvex

namespace MetaMathlibExt

@[expose] public section

/-- **Log-convexity of the n-th roots of generalized Leonardo numbers.** Let $k \ge 1$ be an
integer and let $L_{k,n}$ be the generalized Leonardo numbers. Then the sequence
$(L_{k,n}^{1/n})_{n \ge 9}$ is log-convex:
$(L_{k,n}^{1/n})^2 \le L_{k,n-1}^{1/(n-1)} L_{k,n+1}^{1/(n+1)}$ for every integer $n \ge 10$.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Theorem 3
(`integers-2024-A82-thm-3`). -/
public theorem_wanted genLeonardo_rpow_inv_logConvex (k : ℕ) (hk : 1 ≤ k) (n : ℕ)
    (hn : 10 ≤ n) :
    ((genLeonardo k n : ℝ) ^ ((1 : ℝ) / n)) ^ 2 ≤
      (genLeonardo k (n - 1) : ℝ) ^ ((1 : ℝ) / (n - 1 : ℕ)) *
        (genLeonardo k (n + 1) : ℝ) ^ ((1 : ℝ) / (n + 1 : ℕ))

end

end MetaMathlibExt

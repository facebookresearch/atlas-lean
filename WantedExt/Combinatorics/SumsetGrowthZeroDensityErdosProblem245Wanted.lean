/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sumsets of sets of density zero (Erdős Problem 245)

Erdős Problem 245: let `A ⊆ ℕ` be infinite with `|A ∩ {1, …, N}| = o(N)`. Is `limsup_{N → ∞} |(A +
A) ∩ {1, …, N}| / |A ∩ {1, …, N}| ≥ 3`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Combinatorics.SumsetGrowthZeroDensityErdosProblem245Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #245, https://www.erdosproblems.com/245 (status
PROVED). UnsolvedMath record UM-30006790 (`EP-245`), dataset ulamai/UnsolvedMath v1.8.0.

`limsup ≥ 3` is stated without a real `limsup`, which Lean evaluates as `0` for unbounded sequences:
for every `ε > 0`, infinitely many `N` have `|(A + A) ∩ [1, N]| > (3 - ε) |A ∩ [1, N]|`. Compared
with the formal-conjectures statement `ErdosProblems/245.lean` (an `EReal` limsup, equivalent; no
code imported).
-/

open Filter Topology
open scoped Pointwise

/-- Erdős Problem 245: for every infinite `A ⊆ ℕ` with `|A ∩ [1, N]| = o(N)`,
`limsup_N |(A + A) ∩ [1, N]| / |A ∩ [1, N]| ≥ 3`, stated as: for every `ε > 0`, infinitely many `N`
have `|(A + A) ∩ [1, N]| > (3 - ε) |A ∩ [1, N]|`. -/
def sumsetRatioLimsupAtLeastThree : Prop :=
  ∀ A : Set ℕ, A.Infinite →
    Tendsto (fun N : ℕ => ((A ∩ Set.Icc 1 N).ncard : ℝ) / N) atTop (𝓝 0) →
    ∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ in atTop,
      (3 - ε) * (A ∩ Set.Icc 1 N).ncard < ((A + A) ∩ Set.Icc 1 N).ncard

/--
Resolved true: Freiman proved that the limsup is at least `3`; erdosproblems.com/245 lists the
problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #245,
https://www.erdosproblems.com/245 (status PROVED); resolution: G. A. Freiman, Foundations of a
structural theory of set addition, Transl. Math. Monogr. 37, Amer. Math. Soc. (1973),
erdosproblems.com/245: proved by Freiman [Fr73], https://doi.org/10.1090/mmono/037.
-/
public theorem_wanted sumsetRatioLimsupAtLeastThree_holds : sumsetRatioLimsupAtLeastThree

end MathlibExt.Combinatorics.SumsetGrowthZeroDensityErdosProblem245Wanted

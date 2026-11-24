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

/-- **Erdős Problem 245 on sumsets of sets of density zero.** For $N \in \mathbb{N}$ write
$[1, N] = \{1, \dots, N\}$, and for $A \subseteq \mathbb{N}$ write
$A + A = \{a + b \mid a, b \in A\}$. This is the statement that for every infinite set
$A \subseteq \mathbb{N}$ with $\lvert A \cap [1, N] \rvert / N \to 0$ as $N \to \infty$ and every
real $\varepsilon > 0$, there are infinitely many $N$ with
$\lvert (A + A) \cap [1, N] \rvert > (3 - \varepsilon) \lvert A \cap [1, N] \rvert$. This expresses
$\limsup_{N \to \infty} \lvert (A + A) \cap [1, N] \rvert / \lvert A \cap [1, N] \rvert \ge 3$. -/
def sumsetRatioLimsupAtLeastThree : Prop :=
  ∀ A : Set ℕ, A.Infinite →
    Tendsto (fun N : ℕ => ((A ∩ Set.Icc 1 N).ncard : ℝ) / N) atTop (𝓝 0) →
    ∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ in atTop,
      (3 - ε) * (A ∩ Set.Icc 1 N).ncard < ((A + A) ∩ Set.Icc 1 N).ncard

/-- **Freiman's theorem on sumsets of sets of density zero.** For $N \in \mathbb{N}$ write
$[1, N] = \{1, \dots, N\}$, and for $A \subseteq \mathbb{N}$ write
$A + A = \{a + b \mid a, b \in A\}$. Let $A \subseteq \mathbb{N}$ be an infinite set with
$\lvert A \cap [1, N] \rvert / N \to 0$ as $N \to \infty$. Then for every real $\varepsilon > 0$
there are infinitely many $N$ with
$\lvert (A + A) \cap [1, N] \rvert > (3 - \varepsilon) \lvert A \cap [1, N] \rvert$; that is,
$\limsup_{N \to \infty} \lvert (A + A) \cap [1, N] \rvert / \lvert A \cap [1, N] \rvert \ge 3$.

Source: T. F. Bloom, Erdős Problems, Problem #245, https://www.erdosproblems.com/245 (status
PROVED); resolution: G. A. Freiman, Foundations of a structural theory of set addition, Transl.
Math. Monogr. 37, Amer. Math. Soc. (1973), erdosproblems.com/245: proved by Freiman [Fr73],
https://doi.org/10.1090/mmono/037.
-/
public theorem_wanted sumsetRatioLimsupAtLeastThree_holds : sumsetRatioLimsupAtLeastThree

end MathlibExt.Combinatorics.SumsetGrowthZeroDensityErdosProblem245Wanted

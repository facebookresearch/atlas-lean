/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Union-free families of sets (Erdős Problem 447)

Erdős Problem 447: how large can a family `F` of subsets of `[n]` be with no `A ∪ B = C` for
distinct `A, B, C ∈ F`? Must `|F| = o(2^n)`? Perhaps even `|F| < (1 + o(1)) C(n, ⌊n/2⌋)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Defs

@[expose] public section

namespace MathlibExt.Combinatorics.UnionFreeFamiliesErdosProblem447Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #447, https://www.erdosproblems.com/447 (status PROVED
(LEAN)). UnsolvedMath record UM-30006877 (`EP-447`), dataset ulamai/UnsolvedMath v1.8.0.

`[n]` is `Fin n` and the maximum is an `sSup` over a bounded set. The two yes/no questions are
separate targets, and the opening "how large" is not stated beyond them; `(1 + o(1)) C(n, ⌊n/2⌋)` is
stated as: for every `ε > 0`, eventually `|F| ≤ (1 + ε) C(n, ⌊n/2⌋)`. Compared with the
formal-conjectures statement `ErdosProblems/447.lean` (equivalent; no code imported).
-/

open Asymptotics

/-- `F` is union-free: there are no distinct `A, B, C ∈ F` with `A ∪ B = C`. -/
def IsUnionFree {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, ∀ C ∈ F, A ≠ B → A ≠ C → B ≠ C → A ∪ B ≠ C

/-- The largest size of a union-free family of subsets of `{0, …, n - 1}`. -/
noncomputable def maxUnionFreeSize (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ F : Finset (Finset (Fin n)), IsUnionFree F ∧ F.card = k}

/-- Erdős Problem 447, first question: union-free families of subsets of `[n]` have `o(2^n)`
members. -/
def maxUnionFreeSizeLittleO : Prop :=
  (fun n : ℕ => (maxUnionFreeSize n : ℝ)) =o[Filter.atTop] fun n : ℕ => (2 : ℝ) ^ n

/-- Erdős Problem 447, second question: union-free families of subsets of `[n]` have at most
`(1 + o(1)) C(n, ⌊n/2⌋)` members. -/
def maxUnionFreeSizeCentralBinomial : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
    (maxUnionFreeSize n : ℝ) ≤ (1 + ε) * n.choose (n / 2)

/--
Resolved true: Kleitman's bound `|F| < (1 + o(1)) C(n, ⌊n/2⌋)` gives `|F| = o(2^n)`; Erdős reported
an earlier unpublished proof of this by Sárközy and Szemerédi (erdosproblems.com/447). Source: T. F.
Bloom, Erdős Problems, Problem #447, https://www.erdosproblems.com/447 (status PROVED (LEAN));
resolution: D. Kleitman, Collections of subsets containing no two sets and their union, Proceedings
of the LA Meeting AMS (1971), 153-155, |F| < (1 + o(1)) C(n, ⌊n/2⌋) (erdosproblems.com/447).
-/
public theorem_wanted maxUnionFreeSizeLittleO_holds : maxUnionFreeSizeLittleO

/--
Resolved true: Kleitman proved `|F| < (1 + o(1)) C(n, ⌊n/2⌋)` for union-free families
(erdosproblems.com/447). Source: T. F. Bloom, Erdős Problems, Problem #447,
https://www.erdosproblems.com/447 (status PROVED (LEAN)); resolution: D. Kleitman, Collections of
subsets containing no two sets and their union, Proceedings of the LA Meeting AMS (1971), 153-155,
|F| < (1 + o(1)) C(n, ⌊n/2⌋) (erdosproblems.com/447).
-/
public theorem_wanted maxUnionFreeSizeCentralBinomial_holds : maxUnionFreeSizeCentralBinomial

end MathlibExt.Combinatorics.UnionFreeFamiliesErdosProblem447Wanted

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sets with no element dividing a sum of two larger ones (Erdős Problem 13)

Erdős Problem 13: let `A ⊆ {1, …, N}` contain no `a, b, c` with `a ∣ b + c` and `a < min(b, c)`. Is
`|A| ≤ N/3 + O(1)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MathlibExt.NumberTheory.NoDivisorOfLargerSumErdosProblem13Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #13, https://www.erdosproblems.com/13 (status PROVED
(LEAN)). UnsolvedMath record UM-30006680 (`EP-13`), dataset ulamai/UnsolvedMath v1.8.0.

`b = c` is allowed in the forbidden configuration, as in the source; the constant is absolute.
Compared with the formal-conjectures statement `ErdosProblems/13.lean` (equivalent; no code
imported).
-/

/-- Erdős Problem 13: there is an absolute constant `C` such that every `A ⊆ {1, …, N}` with no
`a, b, c ∈ A` (`b = c` allowed) satisfying `a < min(b, c)` and `a ∣ b + c` has
`|A| ≤ N/3 + C`. -/
def noDivisorOfLargerSumCardBound : Prop :=
  ∃ C : ℝ, ∀ N : ℕ, ∀ A ⊆ Finset.Icc 1 N,
    (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a < b → a < c → ¬ a ∣ b + c) →
      (A.card : ℝ) ≤ N / 3 + C

/--
Resolved true: Bedert proved that a set `A ⊆ [n]` in which no element divides the sum of two larger
elements has `|A| ≤ ⌊n/3⌋ + 1` for `n` sufficiently large (the example `(2N/3, N]` shows `N/3` is
sharp); erdosproblems.com/13 lists the problem as proved. Source: T. F. Bloom, Erdős Problems,
Problem #13, https://www.erdosproblems.com/13 (status PROVED (LEAN)); resolution: B. Bedert, On a
problem of Erdős and Sárközy about sequences with no term dividing the sum of two larger terms,
arXiv:2301.07065 (2023), abstract: |A| ≤ ⌊n/3⌋ + 1 for n sufficiently large; erdosproblems.com/13,
https://arxiv.org/abs/2301.07065.
-/
public theorem_wanted noDivisorOfLargerSumCardBound_holds : noDivisorOfLargerSumCardBound

end MathlibExt.NumberTheory.NoDivisorOfLargerSumErdosProblem13Wanted

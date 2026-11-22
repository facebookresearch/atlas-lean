/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sparse Ramsey 2-complete sets (Erdős Problem 54)

Erdős Problem 54 (Burr and Erdős): a set `A` of integers is Ramsey 2-complete if for every
2-colouring of `A` all large integers are monochromatic sums of elements of `A`. Burr and Erdős
showed `|A ∩ [1, N]| ≤ c (log N) ^ 2` cannot hold for all large `N`, and built `A` with `|A ∩ [1,
N]| < (2 log₂ N) ^ 3`. Improve either bound.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.SparseRamseyCompleteSetErdosProblem54Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #54, https://www.erdosproblems.com/54 (status SOLVED).
UnsolvedMath record UM-30006700 (`EP-54`), dataset ulamai/UnsolvedMath v1.8.0.

The resolution improved the upper bound to the optimal order, and that improvement is the target.
Ramsey completeness is Conlon, Fox and Pham's definition (§1.1.1, after Burr and Erdős): whenever
`A` is partitioned into classes `A₁, A₂`, every sufficiently large integer lies in `Σ(A₁) ∪ Σ(A₂)`,
the sets of sums of finite sets of distinct elements of one class; the class may depend on the
integer, and `N₀` may depend on the colouring.
-/

/-- `A` is Ramsey `2`-complete: for every `2`-colouring of `A`, every sufficiently large integer
is the sum of a finite set of distinct elements of `A` of one colour. The colour may depend on the
integer: with colour classes `A₁, A₂`, every large integer lies in `Σ(A₁) ∪ Σ(A₂)` (Conlon, Fox and
Pham, §1.1.1, following Burr and Erdős); no single class need be complete. -/
def IsRamseyTwoComplete (A : Set ℕ) : Prop :=
  ∀ colour : ℕ → Bool, ∃ N₀ : ℕ, ∀ m : ℕ, N₀ ≤ m → ∃ (b : Bool) (S : Finset ℕ),
    (∀ s ∈ S, s ∈ A ∧ colour s = b) ∧ ∑ s ∈ S, s = m

/-- Erdős Problem 54, improved upper bound: there is a Ramsey `2`-complete set `A` of positive
integers with `|A ∩ [1, N]| ≤ C (log N) ^ 2` for all `N ≥ 2`. -/
def sparseRamseyTwoCompleteExists : Prop :=
  ∃ C : ℝ, ∃ A : Set ℕ, (∀ a ∈ A, 0 < a) ∧ IsRamseyTwoComplete A ∧
    ∀ N : ℕ, 2 ≤ N → ((A ∩ Set.Icc 1 N).ncard : ℝ) ≤ C * Real.log N ^ 2

/--
Resolved true: Conlon, Fox and Pham (Theorem 1.1) constructed, for every `r ≥ 2`, an `r`-Ramsey
complete set with `|A ∩ [n]| ≤ C r (log n) ^ 2` for all `n`, matching the Burr-Erdős lower bound up
to the constant. Source: T. F. Bloom, Erdős Problems, Problem #54, https://www.erdosproblems.com/54
(status SOLVED); resolution: D. Conlon, J. Fox and H. T. Pham, Subset sums, completeness and
colorings, arXiv:2104.14766 (2021), Theorem 1.1: for every r ≥ 2 an r-Ramsey complete A with |A ∩
[n]| ≤ C r log² n for all n, https://arxiv.org/abs/2104.14766.
-/
public theorem_wanted sparseRamseyTwoCompleteExists_holds : sparseRamseyTwoCompleteExists

end MathlibExt.NumberTheory.SparseRamseyCompleteSetErdosProblem54Wanted

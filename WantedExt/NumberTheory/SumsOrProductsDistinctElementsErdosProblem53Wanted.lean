/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sums or products of distinct elements (Erdős Problem 53)

Erdős Problem 53 (Erdős and Szemerédi): for every `k`, if `A ⊆ ℤ` is finite and `|A|` is large in
terms of `k`, are at least `|A| ^ k` integers sums or products of distinct elements of `A`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Powerset

@[expose] public section

namespace MathlibExt.NumberTheory.SumsOrProductsDistinctElementsErdosProblem53Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #53, https://www.erdosproblems.com/53 (status PROVED
(LEAN)). UnsolvedMath record UM-30006699 (`EP-53`), dataset ulamai/UnsolvedMath v1.8.0.

Sums and products are over nonempty subsets of `A`. Compared with the formal-conjectures statement
`ErdosProblems/53.lean` (equivalent; no code imported).
-/

/-- The integers that are the sum or the product of one or more distinct elements of `A`. -/
def sumsAndProducts (A : Finset ℤ) : Finset ℤ :=
  (A.powerset.erase ∅).image (fun B => ∑ b ∈ B, b) ∪
    (A.powerset.erase ∅).image (fun B => ∏ b ∈ B, b)

/-- Erdős Problem 53 (Erdős and Szemerédi): for every `k`, every finite `A ⊆ ℤ` with `|A|` large in
terms of `k` has at least `|A| ^ k` integers that are sums or products of distinct elements of
`A`. -/
def sumsOrProductsPolynomialGrowth : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ A : Finset ℤ, N ≤ A.card → A.card ^ k ≤ (sumsAndProducts A).card

/--
Resolved true: erdosproblems.com/53 records that Chang solved the problem in this form. Source: T.
F. Bloom, Erdős Problems, Problem #53, https://www.erdosproblems.com/53 (status PROVED (LEAN));
resolution: M.-C. Chang, The Erdős-Szemerédi problem on sum set and product set, Annals of Math.
(2003), 939-957, erdosproblems.com/53: solved in this form by Chang,
https://www.erdosproblems.com/53.
-/
public theorem_wanted sumsOrProductsPolynomialGrowth_holds : sumsOrProductsPolynomialGrowth

end MathlibExt.NumberTheory.SumsOrProductsDistinctElementsErdosProblem53Wanted

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sets with distinct subset products (Erdős Problem 795)

Erdős Problem 795: let `g(n)` be the maximal size of `A ⊆ {1, …, n}` such that the products `∏_{a ∈
S} a` are distinct for all `S ⊆ A`. Is it true that `g(n) ≤ π(n) + π(n^{1/2}) + o(n^{1/2} / log n)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.PrimeCounting

@[expose] public section

namespace MathlibExt.NumberTheory.DistinctSubsetProductsErdosProblem795Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #795, https://www.erdosproblems.com/795 (status
PROVED). UnsolvedMath record UM-30007035 (`EP-795`), dataset ulamai/UnsolvedMath v1.8.0.

The page writes `o(x^{1/2} / log n)`, a misprint for `o(n^{1/2} / log n)` (Erdős's earlier bound is
`π(n) + O(n^{1/2} / log n)`). `π(n^{1/2}) = π(⌊√n⌋)`; the `o` term is stated as `ε √n / log n` for
every `ε > 0` and all large `n`. formal-conjectures has no statement of this problem.
-/

/-- Distinct subsets of `A` have distinct products. -/
def HasDistinctSubsetProducts (A : Finset ℕ) : Prop :=
  ∀ S ⊆ A, ∀ T ⊆ A, ∏ a ∈ S, a = ∏ a ∈ T, a → S = T

/-- Erdős Problem 795: `g(n) ≤ π(n) + π(n^{1/2}) + o(n^{1/2} / log n)`, where `g(n)` is the largest
size of a subset of `{1, …, n}` with distinct subset products. -/
def distinctSubsetProductsBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop, ∀ A ⊆ Finset.Icc 1 n,
    HasDistinctSubsetProducts A →
      (A.card : ℝ) ≤ Nat.primeCounting n + Nat.primeCounting (Nat.sqrt n) +
        ε * Real.sqrt n / Real.log n

/--
Resolved true: Raghavan proved `g(n) = π(n) + π(n^{1/2}) + O(n^{5/12})` (Theorem 1.3), and `n^{5/12}
= o(n^{1/2} / log n)`; erdosproblems.com/795 lists the problem as proved. Source: T. F. Bloom, Erdős
Problems, Problem #795, https://www.erdosproblems.com/795 (status PROVED); resolution: R. Raghavan,
Sharp Bounds for Sets with Distinct Subset Products, arXiv:2501.02695 (2025), Theorem 1.3: f(N) =
π(N) + π(N^{1/2}) + O(N^{5/12}) for the largest size f(N) of a subset of [N] with distinct subset
products, answering Question 1.2 (Erdős #795: is f(N) = π(N) + π(N^{1/2}) + o(π(N^{1/2}))?)
affirmatively, https://arxiv.org/abs/2501.02695.
-/
public theorem_wanted distinctSubsetProductsBound_holds : distinctSubsetProductsBound

end MathlibExt.NumberTheory.DistinctSubsetProductsErdosProblem795Wanted

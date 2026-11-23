/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Common values of k(m - k) and l(n - l) (Erdős Problem 443)

Erdős Problem 443: let `m, n ≥ 1`. What is `#({k(m - k) : 1 ≤ k ≤ m/2} ∩ {l(n - l) : 1 ≤ l ≤ n/2})`?
Can it be arbitrarily large? Is it `≤ (mn)^{o(1)}` for all sufficiently large `m, n`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.NumberTheory.ProductSetIntersectionErdosProblem443Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #443, https://www.erdosproblems.com/443 (status PROVED
(LEAN)). UnsolvedMath record UM-30006874 (`EP-443`), dataset ulamai/UnsolvedMath v1.8.0.

Both questions require `m ≠ n` (for `m = n` the two sets coincide and have `⌊m/2⌋` elements); by
symmetry `n < m`. `m/2` is floor division. The two yes/no questions are separate targets; the first
question (the size of the intersection) is not stated. Compared with the formal-conjectures
statement `ErdosProblems/443.lean` (equivalent; no code imported).
-/

/-- The set `{k (m - k) : 1 ≤ k ≤ m / 2}`. -/
def productSet (m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (m / 2)).image fun k => k * (m - k)

/-- Erdős Problem 443, first question: for `m ≠ n` the intersection
`{k (m - k)} ∩ {l (n - l)}` can be arbitrarily large. -/
def productSetIntersectionUnbounded : Prop :=
  ∀ s : ℕ, ∃ m n : ℕ, n < m ∧ s ≤ (productSet n ∩ productSet m).card

/-- Erdős Problem 443, second question: for `m ≠ n` both large the intersection has at most
`(m n)^(o(1))` elements. -/
def productSetIntersectionSubpolynomial : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ m n : ℕ, n₀ < n → n < m →
    ((productSet n ∩ productSet m).card : ℝ) < ((m : ℝ) * n) ^ ε

/--
Resolved true: Hegyvári and Cambie independently showed that for every `s` there are infinitely many
pairs `(m, n)` for which the intersection has exactly `s` elements (erdosproblems.com/443). Source:
T. F. Bloom, Erdős Problems, Problem #443, https://www.erdosproblems.com/443 (status PROVED (LEAN));
resolution: N. Hegyvári, An elementary question of Erdős and Graham, arXiv:2503.24201 (2025); S.
Cambie (independently, unpublished), size ≤ m^{O(1/log log m)} for m > n, and exactly s for
infinitely many pairs (m, n), for every s (erdosproblems.com/443), https://arxiv.org/abs/2503.24201.
-/
public theorem_wanted productSetIntersectionUnbounded_holds : productSetIntersectionUnbounded

/--
Resolved true: they also showed that for `m > n` the intersection has at most `m^{O(1/log log m)}`
elements, which is `(mn)^{o(1)}` (erdosproblems.com/443). Source: T. F. Bloom, Erdős Problems,
Problem #443, https://www.erdosproblems.com/443 (status PROVED (LEAN)); resolution: N. Hegyvári, An
elementary question of Erdős and Graham, arXiv:2503.24201 (2025); S. Cambie (independently,
unpublished), size ≤ m^{O(1/log log m)} for m > n, and exactly s for infinitely many pairs (m, n),
for every s (erdosproblems.com/443), https://arxiv.org/abs/2503.24201.
-/
public theorem_wanted productSetIntersectionSubpolynomial_holds :
    productSetIntersectionSubpolynomial

end MathlibExt.NumberTheory.ProductSetIntersectionErdosProblem443Wanted

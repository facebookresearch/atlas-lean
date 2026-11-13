/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sets without `k + 1` pairwise coprime integers (Erdős Problem 56)

Erdős Problem 56: let `N ≥ p_k`, where `p_k` is the `k`-th prime. Suppose `A ⊆ {1, …, N}` is such
that there are no `k + 1` elements of `A` which are relatively prime. An example is the set of all
multiples of the first `k` primes. Is this the largest such set?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.PairwiseCoprimeFreeSetsErdosProblem56Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #56, https://www.erdosproblems.com/56 (status DISPROVED
(LEAN)). UnsolvedMath record UM-30006702 (`EP-56`), dataset ulamai/UnsolvedMath v1.8.0.

'Relatively prime' means pairwise coprime: the example (multiples of the first `k` primes) contains
`k + 1` integers with no common prime factor, such as `2, 3, 4` for `k = 2`, but no `k + 1` pairwise
coprime ones. 'Largest' is largest cardinality (Ahlswede and Khachatrian's `f(N, k)`); `p_k =
Nat.nth Nat.Prime (k - 1)` for `k ≥ 1`. Compared with the formal-conjectures statement
`ErdosProblems/56.lean` (equivalent; no code imported).
-/

/-- No `k + 1` elements of `A` are pairwise coprime. -/
def NoPairwiseCoprimeSubset (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ S ⊆ A, S.card = k + 1 → ¬ (S : Set ℕ).Pairwise Nat.Coprime

open Classical in
/-- The numbers in `{1, …, N}` divisible by one of the first `k` primes `p₁ = 2, p₂ = 3, …, p_k`
(`p_{i+1} = Nat.nth Nat.Prime i`). -/
noncomputable def firstPrimesMultiples (N k : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun m => ∃ i < k, Nat.nth Nat.Prime i ∣ m

/-- Erdős Problem 56: for `k ≥ 1` and `N ≥ p_k`, no subset of `{1, …, N}` without `k + 1`
pairwise coprime elements is larger than the set of multiples of the first `k` primes. -/
def firstPrimesMultiplesLargest : Prop :=
  ∀ k N : ℕ, 1 ≤ k → Nat.nth Nat.Prime (k - 1) ≤ N → ∀ A ⊆ Finset.Icc 1 N,
    NoPairwiseCoprimeSubset k A → A.card ≤ (firstPrimesMultiples N k).card

/--
Resolved false: Ahlswede and Khachatrian showed, for `k = 212`, that the maximum size `f(N, k)` of a
subset of `{1, …, N}` without `k + 1` pairwise coprime elements can exceed the number of multiples
of the first `k` primes (in a 1995 paper they proved equality for each fixed `k` and all large `N`);
erdosproblems.com/56 lists the problem as disproved, with a Lean proof of the formal-conjectures
statement. Source: T. F. Bloom, Erdős Problems, Problem #56, https://www.erdosproblems.com/56
(status DISPROVED (LEAN)); resolution: R. Ahlswede and L. H. Khachatrian, On extremal sets without
coprimes, Acta Arith. (1994), 89-99, erdosproblems.com/56: disproved for k = 212; R. Ahlswede and L.
H. Khachatrian, Acta Arith. (1995), 77-100, introduction: in [1] they disproved Erdős' conjecture by
showing that the equality f(n, k) = |E(n, k)| does not always hold, and they prove it for all n
large relative to k, https://www.erdosproblems.com/56.
-/
public theorem_wanted firstPrimesMultiplesLargest_refuted : ¬ firstPrimesMultiplesLargest

end MathlibExt.NumberTheory.PairwiseCoprimeFreeSetsErdosProblem56Wanted

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Largest sets with pairwise common factors containing `N` (Erdős Problem 534)

Erdős Problem 534 (Erdős and Graham): what is the largest `A ⊆ {1, …, N}` containing `N` with
`gcd(a, b) > 1` for all distinct `a, b ∈ A`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MathlibExt.NumberTheory.PairwiseCommonFactorSetErdosProblem534Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #534, https://www.erdosproblems.com/534 (status
SOLVED). UnsolvedMath record UM-30006921 (`EP-534`), dataset ulamai/UnsolvedMath v1.8.0.

The answer is Erdős's refined conjecture, proved by Ahlswede and Khachatrian: for `N = q₁^k₁ ⋯
q_r^k_r` (`q₁ < ⋯ < q_r`) the maximum is attained, for some `j`, by the multiples in `[1, N]` of one
of `2 q₁, …, 2 qⱼ, q₁ ⋯ qⱼ`; `j` is encoded by the prime `q = qⱼ`. Each such set contains `N` and
has pairwise common factors, so the bound gives the maximum. Compared with the formal-conjectures
statement `ErdosProblems/534.lean` (equivalent; no code imported).
-/

/-- `A ⊆ {1, …, N}` contains `N` and any two distinct elements of `A` have a common factor. -/
def IsPairwiseNonCoprimeWithTop (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ N ∈ A ∧ ∀ a ∈ A, ∀ b ∈ A, a ≠ b → 1 < Nat.gcd a b

/-- For a prime factor `q` of `N`, with `q₁ < ⋯ < qⱼ = q` the prime factors of `N` up to `q`: the
integers in `[1, N]` that are multiples of at least one of `2 q₁, …, 2 qⱼ, q₁ ⋯ qⱼ`. -/
def ahlswedeKhachatrianSet (N q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun m =>
    (∏ p ∈ N.primeFactors.filter (· ≤ q), p) ∣ m ∨
      ∃ p ∈ N.primeFactors.filter (· ≤ q), 2 * p ∣ m

/-- Erdős Problem 534, Erdős's refined conjecture: for `N ≥ 2` some prime factor `q` of `N` has
every set `A ⊆ {1, …, N}` that contains `N` and has pairwise common factors of size at most that of
the Ahlswede-Khachatrian set of `q` (which is itself such a set). -/
def pairwiseCommonFactorMaxSize : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∃ q ∈ N.primeFactors, ∀ A : Finset ℕ, IsPairwiseNonCoprimeWithTop N A →
    A.card ≤ (ahlswedeKhachatrianSet N q).card

/--
Resolved true: Ahlswede and Khachatrian proved Erdős's refined conjecture that the maximum is
attained by the multiples of one of `2 q₁, …, 2 qⱼ, q₁ ⋯ qⱼ` for some `j` (Erdős's first guess,
`N/p` or the even numbers sharing a factor with `N`, is false). Source: T. F. Bloom, Erdős Problems,
Problem #534, https://www.erdosproblems.com/534 (status SOLVED); resolution: R. Ahlswede and L. H.
Khachatrian, Sets of integers with pairwise common divisor and a factor from a specified set of
primes, Acta Arith. (1996), 259-276, erdosproblems.com/534: Erdős's refined conjecture proved by
Ahlswede and Khachatrian, https://www.erdosproblems.com/534.
-/
public theorem_wanted pairwiseCommonFactorMaxSize_holds : pairwiseCommonFactorMaxSize

end MathlibExt.NumberTheory.PairwiseCommonFactorSetErdosProblem534Wanted

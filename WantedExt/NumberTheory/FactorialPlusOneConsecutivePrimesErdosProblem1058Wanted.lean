/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# `n! + 1` divisible only by the next two primes (Erdős Problem 1058)

Erdős Problem 1058 (Erdős and Stewart): let `2 = p₁ < p₂ < ⋯` be the primes. Are there only finitely
many `n` such that `n ∈ [p_{k-1}, p_k)` and the only primes dividing `n! + 1` are `p_k` and
`p_{k+1}`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.FactorialPlusOneConsecutivePrimesErdosProblem1058Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1058, https://www.erdosproblems.com/1058 (status
PROVED). UnsolvedMath record UM-30007149 (`EP-1058`), dataset ulamai/UnsolvedMath v1.8.0.

Primes are indexed from `0` by `Nat.nth Nat.Prime`, and `n` is a positive integer (for the first
prime the interval is `[1, 2)`). "The only primes dividing `n! + 1` are `p_k` and `p_{k+1}`" is read
as: every prime factor is one of them (the solutions `n = 1, …, 5` include `4! + 1 = 5²` and
`5! + 1 = 11²`). This set contains the set of the reading where both primes must divide, so its
finiteness is the stronger statement. Compared with the formal-conjectures statement
`ErdosProblems/1058.lean` (equivalent; no code imported).
-/

/-- `n ≥ 1` lies in `[p_{k-1}, p_k)` for the `k`-th prime `p_k` (here `Nat.nth Nat.Prime k`,
indexed from `0`; for `k = 0` the interval is `[1, 2)`) and every prime factor of `n! + 1` is `p_k`
or `p_{k+1}`. -/
def IsErdosStewartSolution (n : ℕ) : Prop :=
  0 < n ∧ ∃ k : ℕ, (k = 0 ∨ Nat.nth Nat.Prime (k - 1) ≤ n) ∧ n < Nat.nth Nat.Prime k ∧
    ∀ r : ℕ, r.Prime → r ∣ n.factorial + 1 → r = Nat.nth Nat.Prime k ∨ r = Nat.nth Nat.Prime (k + 1)

/-- Erdős Problem 1058 (Erdős and Stewart): only finitely many `n` have this property. -/
def erdosStewartSolutionsFinite : Prop :=
  {n : ℕ | IsErdosStewartSolution n}.Finite

/--
Resolved true: Luca proved that `n = 1, 2, 3, 4, 5` are the only solutions; erdosproblems.com/1058
lists the problem as proved, with a formal proof in plby/lean-proofs (`Erdos1058.lean`). Source: T.
F. Bloom, Erdős Problems, Problem #1058, https://www.erdosproblems.com/1058 (status PROVED);
resolution: F. Luca, On a conjecture of Erdős and Stewart, Math. Comp. (2001), 893-896, the only
solutions are n = 1, 2, 3, 4, 5 (erdosproblems.com/1058),
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1058.lean#L47.
-/
public theorem_wanted erdosStewartSolutionsFinite_holds : erdosStewartSolutionsFinite

end MathlibExt.NumberTheory.FactorialPlusOneConsecutivePrimesErdosProblem1058Wanted

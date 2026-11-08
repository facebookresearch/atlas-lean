/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Data.ZMod.Basic

/-!
# Sparse subsets of powers with no prime translate

Theorem 1 of Desmond Weisenberg, *Sparse Admissible Sets and a Problem of Erdős and Graham*,
INTEGERS 24 (2024), Article A89 (the set `S` read from arXiv:2405.12310v2). Its closing
consequence, the refutation of Erdős Problem 429, is `erdos429_refuted` in
`WantedExt/NumberTheory/ErdosProblem429Wanted.lean`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- Let `a` be a natural number that is a primitive root modulo infinitely many primes (this
forces `a ≥ 2`), and `S = {a^k : k ≥ 1}`. For every non-decreasing unbounded `f : ℕ → ℕ` there
is an infinite `A ⊆ S` with `|A ∩ {1, …, N}| ≤ f(N)` for all `N` such that no translate `A + n` (`n ∈ ℤ`)
consists of (positive) primes. The exponent range `k ≥ 1` is the reading in which the paper's
remark "`S` is admissible" holds: with `k = 0` and `a` even, `S ∋ 1, a` meets both classes
mod `2`.

Source: Desmond Weisenberg, *Sparse Admissible Sets and a Problem of Erdős and Graham*,
INTEGERS 24 (2024), Article A89, Theorem 1 (`integers-2024-A89-thm-1`). -/
public theorem_wanted exists_sparse_subset_pow_no_prime_translate {a : ℕ}
    (hprim : {p : ℕ | p.Prime ∧ IsPrimitiveRoot (a : ZMod p) (p - 1)}.Infinite)
    {f : ℕ → ℕ} (hmono : Monotone f) (hunb : ∀ M : ℕ, ∃ N : ℕ, M ≤ f N) :
    ∃ A : Set ℕ, A.Infinite ∧ A ⊆ {m | ∃ k : ℕ, 1 ≤ k ∧ m = a ^ k} ∧
      (∀ N : ℕ, (A ∩ Set.Icc 1 N).ncard ≤ f N) ∧
      ¬ ∃ n : ℤ, ∀ m ∈ A, ∃ p : ℕ, p.Prime ∧ (p : ℤ) = m + n

end

end MetaMathlibExt

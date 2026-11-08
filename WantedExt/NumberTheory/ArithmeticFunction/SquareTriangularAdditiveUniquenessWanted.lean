/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-!
# Squares and triangular numbers as an additive uniqueness pair

Statements from Mingyu Kim and Poo-Sung Park, *An Additive Uniqueness Pair of Sets for
Multiplicative Functions: Squares and Triangular Numbers*, INTEGERS 26 (2026), Article A103.
The paper's `t_v` is the `v`-th triangular number `v (v + 1) / 2`; this indexing is the one
for which the paper's Lemma 1 `n² + t_{n-2} = (n-1)² + t_n` holds. Multiplicative functions
are `ArithmeticFunction ℂ` with `IsMultiplicative`.
-/

namespace MetaMathlibExt

@[expose] public section

open ArithmeticFunction

/-- For `n ≥ 2`, `n² + t_{n-2} = (n - 1)² + t_n`, with `t_v = v (v + 1) / 2`.

Source: Mingyu Kim and Poo-Sung Park, *An Additive Uniqueness Pair of Sets for
Multiplicative Functions: Squares and Triangular Numbers*, INTEGERS 26 (2026), Article A103,
Lemma 1 (`integers-2026-A103-lem-1`). -/
public theorem_wanted sq_add_triangular_sub_two_eq (n : ℕ) (hn : 2 ≤ n) :
    n ^ 2 + (n - 2) * (n - 2 + 1) / 2 = (n - 1) ^ 2 + n * (n + 1) / 2

/-- Let `f` be multiplicative with `f (u² + t_v) = f (u²) + f (t_v)` for all positive
`u, v`. If `N ≥ 3` and `f n = n` for `1 ≤ n ≤ N - 1`, then `f (m²) = m²` for every `m` with
`1 ≤ m ≤ N - 2`.

Source: Mingyu Kim and Poo-Sung Park, *An Additive Uniqueness Pair of Sets for
Multiplicative Functions: Squares and Triangular Numbers*, INTEGERS 26 (2026), Article A103,
Lemma 2 (`integers-2026-A103-lem-2`). -/
public theorem_wanted multiplicative_sq_triangular_additive_sq
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ u v : ℕ, 0 < u → 0 < v →
      f (u ^ 2 + v * (v + 1) / 2) = f (u ^ 2) + f (v * (v + 1) / 2))
    (N : ℕ) (hN : 3 ≤ N) (hlt : ∀ n : ℕ, 1 ≤ n → n ≤ N - 1 → f n = n)
    (m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N - 2) :
    f (m ^ 2) = m ^ 2

/-- Let `f` be multiplicative with `f (u² + t_v) = f (u²) + f (t_v)` for all positive
`u, v`. If `N ≥ 4` and `f n = n` for `1 ≤ n ≤ N - 1`, then `f (2^(2k-1)) = 2^(2k-1)` for
every positive `k` with `2k ≤ N - 2`.

Source: Mingyu Kim and Poo-Sung Park, *An Additive Uniqueness Pair of Sets for
Multiplicative Functions: Squares and Triangular Numbers*, INTEGERS 26 (2026), Article A103,
Lemma 3 (`integers-2026-A103-lem-3`). -/
public theorem_wanted multiplicative_sq_triangular_additive_two_pow_odd
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ u v : ℕ, 0 < u → 0 < v →
      f (u ^ 2 + v * (v + 1) / 2) = f (u ^ 2) + f (v * (v + 1) / 2))
    (N : ℕ) (hN : 4 ≤ N) (hlt : ∀ n : ℕ, 1 ≤ n → n ≤ N - 1 → f n = n)
    (k : ℕ) (hk : 0 < k) (hkN : 2 * k ≤ N - 2) :
    f (2 ^ (2 * k - 1)) = 2 ^ (2 * k - 1)

/-- A multiplicative function with `f (u² + t_v) = f (u²) + f (t_v)` for all positive
`u, v` is the identity.

Source: Mingyu Kim and Poo-Sung Park, *An Additive Uniqueness Pair of Sets for
Multiplicative Functions: Squares and Triangular Numbers*, INTEGERS 26 (2026), Article A103,
Theorem 1 (`integers-2026-A103-thm-1`). -/
public theorem_wanted multiplicative_sq_triangular_additive_eq_id
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ u v : ℕ, 0 < u → 0 < v →
      f (u ^ 2 + v * (v + 1) / 2) = f (u ^ 2) + f (v * (v + 1) / 2)) :
    ∀ n : ℕ, f n = n

end

end MetaMathlibExt

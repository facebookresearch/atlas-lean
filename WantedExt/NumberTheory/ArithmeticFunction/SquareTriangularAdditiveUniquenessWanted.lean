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

/-- **A square–triangular number identity.** Let $t_v = v(v + 1)/2$ denote the $v$-th triangular
number. For every natural number $n \ge 2$, $n^2 + t_{n-2} = (n - 1)^2 + t_n$.

Source: Mingyu Kim and Poo-Sung Park, *An Additive Uniqueness Pair of Sets for
Multiplicative Functions: Squares and Triangular Numbers*, INTEGERS 26 (2026), Article A103,
Lemma 1 (`integers-2026-A103-lem-1`). -/
public theorem_wanted sq_add_triangular_sub_two_eq (n : ℕ) (hn : 2 ≤ n) :
    n ^ 2 + (n - 2) * (n - 2 + 1) / 2 = (n - 1) ^ 2 + n * (n + 1) / 2

/-- **Square–triangular additivity fixes small squares.** Let $t_v = v(v + 1)/2$ denote the
$v$-th triangular number, and let $f$ be a complex-valued multiplicative arithmetic function
with $f(u^2 + t_v) = f(u^2) + f(t_v)$ for all positive integers $u$ and $v$. Let $N \ge 3$ be an
integer such that $f(n) = n$ for every integer $n$ with $1 \le n \le N - 1$. Then
$f(m^2) = m^2$ for every integer $m$ with $1 \le m \le N - 2$.

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

/-- **Square–triangular additivity fixes odd powers of two.** Let $t_v = v(v + 1)/2$ denote the
$v$-th triangular number, and let $f$ be a complex-valued multiplicative arithmetic function
with $f(u^2 + t_v) = f(u^2) + f(t_v)$ for all positive integers $u$ and $v$. Let $N \ge 4$ be an
integer such that $f(n) = n$ for every integer $n$ with $1 \le n \le N - 1$. Then
$f(2^{2k-1}) = 2^{2k-1}$ for every positive integer $k$ with $2k \le N - 2$.

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

/-- **Squares and triangular numbers are an additive uniqueness pair.** Let $t_v = v(v + 1)/2$
denote the $v$-th triangular number. If $f$ is a complex-valued multiplicative arithmetic
function with $f(u^2 + t_v) = f(u^2) + f(t_v)$ for all positive integers $u$ and $v$, then
$f(n) = n$ for every natural number $n$.

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

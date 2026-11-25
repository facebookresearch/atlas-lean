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
public import MathlibExt.NumberTheory.ArithmeticFunction.SquareTriangularAdditiveUniqueness
public import MathlibExt.NumberTheory.ArithmeticFunction.SquareTriangularOddPowers
public import MathlibExt.NumberTheory.ArithmeticFunction.SquareTriangularSmallSquares

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

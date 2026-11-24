/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.ArithmeticFunction.MultiplicativeAdditiveOnSquares

/-!
# Multiplicative functions additive on squares and on sums of consecutive squares

Statements from Elchin Hasanalizade, *On the k-Additive Uniqueness of Sums of Consecutive
Squares for Multiplicative Functions*, INTEGERS 25 (2025), Article A40. Multiplicative
functions are `ArithmeticFunction ℂ` with `IsMultiplicative` (which includes `f 1 = 1`).
The paper's set `T = {s_m - s_n : m > n ≥ 0}` with `s_n = ∑_{i=0}^{n} i²` is written as
the sums `∑ j ∈ Finset.Ioc n m, j ^ 2` with `n < m`.
-/

namespace MetaMathlibExt

@[expose] public section

open ArithmeticFunction

/-- **Sums of consecutive squares form a $k$-additive uniqueness set for every $k \ge 2$.** Let
$k \ge 2$, and call a natural number a sum of consecutive squares if it equals
$(n+1)^2 + (n+2)^2 + \dots + m^2$ for some natural numbers $n < m$. Let $f$ be a complex-valued
multiplicative arithmetic function (so $f(1) = 1$ and $f(ab) = f(a) f(b)$ for coprime $a$ and
$b$). If $f(x_1 + \dots + x_k) = f(x_1) + \dots + f(x_k)$ for all sums of consecutive squares
$x_1, \dots, x_k$, then $f(n) = n$ for every natural number $n$.

Source: Elchin Hasanalizade, *On the k-Additive Uniqueness of Sums of Consecutive Squares
for Multiplicative Functions*, INTEGERS 25 (2025), Article A40, Theorem 2
(`integers-2025-A40-thm-2`). -/
public theorem_wanted consecutiveSquareSums_kAdditiveUniqueness (k : ℕ) (hk : 2 ≤ k)
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ x : Fin k → ℕ, (∀ i, ∃ m n : ℕ, n < m ∧ x i = ∑ j ∈ Finset.Ioc n m, j ^ 2) →
      f (∑ i, x i) = ∑ i, f (x i)) :
    ∀ n : ℕ, f n = n

end

end MetaMathlibExt

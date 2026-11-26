/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import MathlibExt.NumberTheory.IntegerComplexityBounds

/-!
# A lower-bound criterion for integer complexity

A function bounded by the sum of its values on the operands of both operations is bounded
by the number of ones in every expression, and hence by integer complexity.
-/

namespace MathlibExt.NumberTheory.IntegerComplexityWanted

open IntegerComplexity

/-- **A criterion for lower bounds on integer complexity.** Write $\lVert n \rVert$ for the
integer complexity of a positive integer $n$, the least number of ones needed to write $n$ using
$1$, $+$, $\times$ and parentheses. Let $P$ be a real-valued function on the natural numbers with
$P(1) = 1$ such that $P(n + m) \le P(n) + P(m)$ and $P(nm) \le P(n) + P(m)$ for all positive
integers $n$ and $m$. Then $P(n) \le \lVert n \rVert$ for every positive integer $n$.

Source: Juan Arias de Reyna, "Complexity of Natural
Numbers", Proposition 2. -/
public theorem le_complexity_of_subadditive (P : ℕ → ℝ)
    (h1 : P 1 = 1)
    (hadd : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → P (n + m) ≤ P n + P m)
    (hmul : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → P (n * m) ≤ P n + P m)
    (n : ℕ) (hn : 1 ≤ n) :
    P n ≤ (cx n : ℝ) := by
  have hbound (e : Expr) : P e.eval ≤ (e.count : ℝ) := by
    induction e with
    | one => simp [h1]
    | add a b ha hb =>
      simpa only [Expr.eval_add, Expr.count_add, Nat.cast_add] using
        (hadd a.eval b.eval a.eval_pos b.eval_pos).trans (add_le_add ha hb)
    | mul a b ha hb =>
      simpa only [Expr.eval_mul, Expr.count_mul, Nat.cast_add] using
        (hmul a.eval b.eval a.eval_pos b.eval_pos).trans (add_le_add ha hb)
  obtain ⟨e, he, hc⟩ := exists_optimal ⟨n, hn⟩
  change e.eval = n at he
  rw [cx, dite_eq_left (show 0 < n from hn), ← hc, ← he]
  exact hbound e

end MathlibExt.NumberTheory.IntegerComplexityWanted

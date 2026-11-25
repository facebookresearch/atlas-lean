/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import MathlibExt.NumberTheory.IntegerComplexityBounds

/-!
# A logarithmic lower bound for integer complexity

An expression with `k` ones has value at most `2 ^ k - 1`, giving a base-two logarithmic
lower bound on the number of ones needed to represent a positive integer.
-/

namespace MathlibExt.NumberTheory.IntegerComplexityWanted

private theorem one_add_eval_le_two_pow_count (e : IntegerComplexity.Expr) :
    1 + e.eval ≤ 2 ^ e.count := by
  induction e with
  | one => decide
  | add a b ha hb =>
    rw [IntegerComplexity.Expr.eval_add, IntegerComplexity.Expr.count_add, pow_add]
    calc
      1 + (a.eval + b.eval) ≤ (1 + a.eval) * (1 + b.eval) := by grind
      _ ≤ 2 ^ a.count * 2 ^ b.count := Nat.mul_le_mul ha hb
  | mul a b ha hb =>
    rw [IntegerComplexity.Expr.eval_mul, IntegerComplexity.Expr.count_mul, pow_add]
    calc
      1 + a.eval * b.eval ≤ (1 + a.eval) * (1 + b.eval) := by grind
      _ ≤ 2 ^ a.count * 2 ^ b.count := Nat.mul_le_mul ha hb

/-- **Logarithmic lower bound for integer complexity.** Write $\lVert n \rVert$ for the integer
complexity of a positive integer $n$, the least number of ones needed to write $n$ using $1$, $+$,
$\times$ and parentheses. For every positive integer $n$, $\log_2(1 + n) \le \lVert n \rVert$.

Source: Juan Arias de Reyna, "Complexity of Natural
Numbers", Corollary 1. -/
public theorem logb_two_add_one_le (n : ℕ) (hn : 1 ≤ n) :
    Real.logb 2 (1 + n) ≤ (cx n : ℝ) := by
  obtain ⟨e, he, hc⟩ := IntegerComplexity.exists_optimal ⟨n, hn⟩
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_natCast]
  rw [cx, dite_eq_left (show 0 < n from hn), ← hc]
  have h := one_add_eval_le_two_pow_count e
  rw [he] at h
  exact_mod_cast h

end MathlibExt.NumberTheory.IntegerComplexityWanted

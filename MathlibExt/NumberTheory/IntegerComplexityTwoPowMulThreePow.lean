/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.IntegerComplexityBounds
import Mathlib.Tactic.IntervalCases

/-!
# Integer complexity of `2 ^ a * 3 ^ b` for `a ≤ 2`

The main result, `complexity_two_pow_mul_three_pow`, shows that the integer complexity of
`2 ^ a * 3 ^ b` is `2 * a + 3 * b` when `a ≤ 2` and `a`, `b` are not both zero. Juan Arias de
Reyna derives this in *Complexity of Natural Numbers* (https://arxiv.org/abs/2111.03345) as a
corollary of his proposition on extremal expressions, stated there for every natural number `b`;
the case `a = b = 0` is excluded here since the complexity of `1` is `1`.

The upper bound multiplies the expressions `1 + 1` and `1 + (1 + 1)`. For the lower bound, the
extremal value `2 ^ a' * 3 ^ b'` for a budget of `2 * a + 3 * b - 1` ones lies below
`2 ^ a * 3 ^ b`, so `complexity_lt_of_gt_extremal` applies; at `2`, where that budget is a single
one, `complexityLowerBoundG_le` gives the bound instead.
-/

set_option autoImplicit false

namespace MathlibExt.NumberTheory.IntegerComplexityWanted

namespace complexity_two_pow_mul_three_pow

open IntegerComplexity

/-- Products of `1 + 1` and `1 + (1 + 1)` write `2 ^ a * 3 ^ b` with `2 * a + 3 * b` ones. -/
private theorem exists_expr_eval_count (a b : ℕ) (ha : a ≤ 2) (hab : 1 ≤ 2 * a + 3 * b) :
    ∃ e : Expr, e.eval = 2 ^ a * 3 ^ b ∧ e.count = 2 * a + 3 * b := by
  induction b with
  | zero =>
    interval_cases a
    · omega
    · exact ⟨.add .one .one, rfl, rfl⟩
    · exact ⟨.mul (.add .one .one) (.add .one .one), rfl, rfl⟩
  | succ b ih =>
    by_cases h : 1 ≤ 2 * a + 3 * b
    · obtain ⟨e, he, hc⟩ := ih h
      refine ⟨.mul e (.add .one (.add .one .one)), ?_, ?_⟩
      · simp only [Expr.eval_mul, Expr.eval_add, Expr.eval_one, he, pow_succ, Nat.mul_assoc]
      · simp only [Expr.count_mul, Expr.count_add, Expr.count_one, hc]
        omega
    · obtain rfl : a = 0 := by omega
      obtain rfl : b = 0 := by omega
      exact ⟨.add .one (.add .one .one), rfl, rfl⟩

end complexity_two_pow_mul_three_pow

open complexity_two_pow_mul_three_pow in
/-- **Integer complexity of $2^a 3^b$ for $a \le 2$.** Write $\lVert n \rVert$ for the integer
complexity of a positive integer $n$, the least number of ones needed to write $n$ using $1$, $+$,
$\times$ and parentheses. For all natural numbers $a \le 2$ and $b$, not both zero,
$\lVert 2^a 3^b \rVert = 2a + 3b$.

Source: Juan Arias de Reyna, "Complexity of Natural
Numbers", Corollary 2. -/
public theorem complexity_two_pow_mul_three_pow (a b : ℕ)
    (ha : a ≤ 2) (hab : 1 ≤ 2 * a + 3 * b) :
    cx (2 ^ a * 3 ^ b) = 2 * a + 3 * b := by
  apply le_antisymm
  · -- An explicit expression gives the upper bound.
    obtain ⟨e, he, hc⟩ := exists_expr_eval_count a b ha hab
    rw [cx, dite_eq_left (he ▸ e.eval_pos), ← hc]
    exact IntegerComplexity.complexity_le he
  · -- `2 ^ a * 3 ^ b` exceeds the extremal value for one fewer one.
    have hpos : 0 < 3 ^ b := Nat.pow_pos (by decide)
    obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by omega
    · obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
      have h := complexity_lt_of_gt_extremal 1 k (2 ^ 0 * 3 ^ (k + 1)) (by decide) (by omega)
        (by rw [Nat.pow_succ] at hpos ⊢; omega)
      omega
    · rcases b with _ | k
      · have h := complexityLowerBoundG_le 2 (by decide)
        have hg : complexityLowerBoundG 2 = 2 := by decide
        change 2 ≤ cx 2
        omega
      · have h := complexity_lt_of_gt_extremal 2 k (2 ^ 1 * 3 ^ (k + 1)) le_rfl (by omega)
          (by rw [Nat.pow_succ] at hpos ⊢; omega)
        omega
    · have h := complexity_lt_of_gt_extremal 0 (b + 1) (2 ^ 2 * 3 ^ b) (by decide) (by omega)
        (by rw [Nat.pow_succ]; omega)
      omega

end MathlibExt.NumberTheory.IntegerComplexityWanted

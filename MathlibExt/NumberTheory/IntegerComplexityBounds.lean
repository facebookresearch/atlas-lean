/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Log
public import MathlibExt.NumberTheory.IntegerComplexity
import Mathlib.Tactic.IntervalCases

/-!
# Extremal bounds for integer complexity

For a budget of at least two ones, adding three ones triples the extremal value.
Starting with budgets of two, three and four gives the three families of bounds in
Juan Arias de Reyna's *Complexity of Natural Numbers* (https://arxiv.org/abs/2111.03345).
-/

set_option autoImplicit false

namespace MathlibExt.NumberTheory.IntegerComplexityWanted

@[expose] public section

/-- **Integer complexity extended to all natural numbers.** For a natural number $n$, the value
$\lVert n \rVert$ is the integer complexity of $n$ when $n$ is positive, that is, the least number
of ones needed to write $n$ using $1$, $+$, $\times$ and parentheses, and $\lVert 0 \rVert = 0$. -/
noncomputable def cx (n : ℕ) : ℕ :=
  if h : 0 < n then IntegerComplexity.complexity ⟨n, h⟩ else 0

/-- **Lower-bound function for integer complexity.** For a natural number $n$, let $a$ be the
largest natural number with $3^a \le n$ when $n \ge 1$, and let $a = 0$ when $n = 0$. The function
$g$ on the natural numbers is given by $g(n) = 3a$ if $n < \frac{4}{3} \cdot 3^a$,
$g(n) = 3a + 1$ if $\frac{4}{3} \cdot 3^a \le n < 2 \cdot 3^a$, and $g(n) = 3a + 2$ if
$n \ge 2 \cdot 3^a$. -/
def complexityLowerBoundG (n : ℕ) : ℕ :=
  let a := Nat.log 3 n
  if 3 * (n - 3 ^ a) < 3 ^ a then 3 * a
  else if n < 2 * 3 ^ a then 3 * a + 1
  else 3 * a + 2

end

namespace complexity_lt_of_gt_extremal

/-- Upper bound for the value of an expression with a given number of ones. -/
private def bound : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | n + 5 => bound (n + 2) * 3

private theorem bound_add_three (n : ℕ) (hn : 2 ≤ n) :
    bound (n + 3) = bound n * 3 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rfl

/-- Both expression constructors respect the bound at the combined budget. -/
private theorem bound_combine (i j : ℕ) :
    bound i + bound j ≤ bound (i + j) ∧ bound i * bound j ≤ bound (i + j) := by
  -- Reduce the larger budget by three until both budgets are at most four.
  by_cases hij : j < i
  · simpa only [Nat.add_comm j i, Nat.add_comm (bound j) (bound i),
      Nat.mul_comm (bound j) (bound i)] using bound_combine j i
  by_cases hj : j < 5
  · have hi : i < 5 := by omega
    interval_cases i <;> interval_cases j <;> decide
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 + 3 := ⟨j - 5, by omega⟩
  obtain ⟨hs, hp⟩ := bound_combine i (k + 2)
  rw [← Nat.add_assoc, bound_add_three (k + 2) (by omega),
    bound_add_three (i + (k + 2)) (by omega)]
  constructor
  · omega
  · rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right 3 hp
termination_by (i + j, i)
decreasing_by
  · rw [Nat.add_comm j i]
    exact Prod.Lex.right _ hij
  · exact Prod.Lex.left _ _ (by omega)

private theorem eval_le_bound (e : IntegerComplexity.Expr) : e.eval ≤ bound e.count := by
  induction e with
  | one => decide
  | add x y hx hy => exact (Nat.add_le_add hx hy).trans (bound_combine x.count y.count).1
  | mul x y hx hy => exact (Nat.mul_le_mul hx hy).trans (bound_combine x.count y.count).2

private theorem bound_extremal (a b : ℕ) (ha : a ≤ 2) (hab : 2 ≤ 2 * a + 3 * b) :
    bound (2 * a + 3 * b) = 2 ^ a * 3 ^ b := by
  induction b with
  | zero => interval_cases a <;> first | decide | omega
  | succ b ih =>
    by_cases h : 2 ≤ 2 * a + 3 * b
    · rw [Nat.mul_succ, ← Nat.add_assoc, bound_add_three _ h, ih h, pow_succ, Nat.mul_assoc]
    · obtain rfl : a = 0 := by omega
      obtain rfl : b = 0 := by omega
      decide

end complexity_lt_of_gt_extremal

open complexity_lt_of_gt_extremal in
/-- **Integers above $2^a 3^b$ have complexity above $2a + 3b$ when $a \le 2$ and $2a + 3b \ge 2$.**
Write $\lVert m \rVert$ for the integer complexity of a positive integer $m$, the least number
of ones needed to write $m$ using $1$, $+$, $\times$ and parentheses. Let $a \le 2$ and $b$ be
natural numbers with $2a + 3b \ge 2$. Then every natural number $m > 2^a 3^b$ satisfies
$\lVert m \rVert > 2a + 3b$.

Source: Juan Arias de Reyna, "Complexity of Natural
Numbers", Corollary 2. -/
public theorem complexity_lt_of_gt_extremal (a b m : ℕ)
    (ha : a ≤ 2) (hab : 2 ≤ 2 * a + 3 * b)
    (hm : 2 ^ a * 3 ^ b < m) :
    2 * a + 3 * b < cx m := by
  have hm_pos : 0 < m := Nat.zero_lt_of_lt hm
  rw [cx, dite_eq_left hm_pos]
  obtain ⟨e, he, hc⟩ := IntegerComplexity.exists_optimal ⟨m, hm_pos⟩
  have hmono : Monotone bound := monotone_nat_of_le_succ fun n =>
    (Nat.le_add_right (bound n) (bound 1)).trans (bound_combine n 1).1
  apply lt_of_not_ge
  intro h
  exact hm.not_ge <| calc
    m = e.eval := he.symm
    _ ≤ bound e.count := eval_le_bound e
    _ ≤ bound (2 * a + 3 * b) := hmono (hc.trans_le h)
    _ = 2 ^ a * 3 ^ b := bound_extremal a b ha hab

end MathlibExt.NumberTheory.IntegerComplexityWanted

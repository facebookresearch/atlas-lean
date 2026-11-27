/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Bounds.Defs
public import MathlibExt.NumberTheory.IntegerComplexityBounds

/-!
# The recurrence for integer complexity

The complexity of a natural number at least two is the least combined complexity of its
factor pairs and additive splits.
-/

namespace MathlibExt.NumberTheory.IntegerComplexityWanted

open IntegerComplexity

namespace complexity_eq_min

private theorem cx_add_le {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    cx (a + b) ≤ cx a + cx b := by
  simp only [cx, dite_eq_left ha, dite_eq_left hb, dite_eq_left (Nat.add_pos_left ha b)]
  exact complexity_add_le ⟨a, ha⟩ ⟨b, hb⟩

private theorem cx_mul_le {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    cx (a * b) ≤ cx a + cx b := by
  simp only [cx, dite_eq_left ha, dite_eq_left hb, dite_eq_left (Nat.mul_pos ha hb)]
  exact complexity_mul_le ⟨a, ha⟩ ⟨b, hb⟩

private theorem cx_eval_le_count (e : Expr) : cx e.eval ≤ e.count := by
  rw [cx, dite_eq_left e.eval_pos]
  exact complexity_le (n := ⟨e.eval, e.eval_pos⟩) (e := e) rfl

end complexity_eq_min

open complexity_eq_min in
/-- **Integer complexity as a minimum over factorizations and sums.** Write
$\lVert m \rVert$ for the integer complexity of a positive integer $m$, the least number of ones
needed to write $m$ using $1$, $+$, $\times$ and parentheses. For every integer $n \ge 2$,
$\lVert n \rVert$ is the least element of the set consisting of the numbers
$\lVert d \rVert + \lVert n/d \rVert$ for the divisors $d \ge 2$ of $n$ and the numbers
$\lVert j \rVert + \lVert n - j \rVert$ for the integers $j$ with $1 \le j \le n/2$.

Source: Juan Arias de Reyna, "Complexity of Natural
Numbers", Proposition 1. -/
public theorem complexity_eq_min (n : ℕ) (hn : 2 ≤ n) :
    IsLeast {k | (∃ d : ℕ, 2 ≤ d ∧ d ∣ n ∧
        k = cx d + cx (n / d)) ∨
      (∃ j : ℕ, 1 ≤ j ∧ j ≤ n / 2 ∧ k = cx j + cx (n - j))}
      (cx n) := by
  have hn_pos : 0 < n := by omega
  constructor
  · obtain ⟨e, he, hc⟩ := exists_optimal ⟨n, hn_pos⟩
    change e.eval = n at he
    have hcount : e.count = cx n := by simpa only [cx, dite_eq_left hn_pos] using hc
    cases e with
    | one =>
      simp only [Expr.eval_one] at he
      omega
    | add x y =>
      change x.eval + y.eval = n at he
      change x.count + y.count = cx n at hcount
      have hcost : cx n = cx x.eval + cx y.eval := le_antisymm
        (he ▸ cx_add_le x.eval_pos y.eval_pos)
        (hcount ▸ Nat.add_le_add (cx_eval_le_count x) (cx_eval_le_count y))
      right
      refine ⟨min x.eval y.eval, le_min x.eval_pos y.eval_pos, by omega, ?_⟩
      rcases le_total x.eval y.eval with h | h
      · rwa [min_eq_left h, show n - x.eval = y.eval by omega]
      · rwa [min_eq_right h, show n - y.eval = x.eval by omega, add_comm]
    | mul x y =>
      change x.eval * y.eval = n at he
      change x.count + y.count = cx n at hcount
      -- A factor of value one could be removed, saving its entire positive count.
      have hx : 2 ≤ x.eval := by
        by_contra! h
        have hx_one : x.eval = 1 := by
          have := x.eval_pos
          omega
        rw [hx_one, one_mul] at he
        have hy := cx_eval_le_count y
        rw [he] at hy
        have := x.count_pos
        omega
      left
      refine ⟨x.eval, hx, ⟨y.eval, he.symm⟩, ?_⟩
      rw [← he, Nat.mul_div_cancel_left _ x.eval_pos]
      apply le_antisymm (cx_mul_le x.eval_pos y.eval_pos)
      rw [he, ← hcount]
      exact Nat.add_le_add (cx_eval_le_count x) (cx_eval_le_count y)
  · rintro k (⟨d, hd, ⟨q, rfl⟩, rfl⟩ | ⟨j, hj, hjn, rfl⟩)
    · have hd_pos : 0 < d := by omega
      have hq_pos : 0 < q := by
        by_contra! h
        simp [show q = 0 by omega] at hn
      rw [Nat.mul_div_cancel_left _ hd_pos]
      exact cx_mul_le hd_pos hq_pos
    · have hsum : j + (n - j) = n := by omega
      simpa only [hsum] using cx_add_le (a := j) (b := n - j) hj (by omega)

end MathlibExt.NumberTheory.IntegerComplexityWanted

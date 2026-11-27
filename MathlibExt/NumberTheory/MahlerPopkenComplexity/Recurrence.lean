/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.MahlerPopkenComplexity

/-!
# Recurrence for Mahler–Popken complexity

The $m$-ary complexity satisfies Campbell's recurrence for $m \ge 1$ and $n > m$.
An optimal expression for such an $n$ has a sum or product at its root,
and a factor of value one can be removed to give a shorter expression.
-/

set_option autoImplicit false

public section

namespace MathlibExt.NumberTheory.MahlerPopkenComplexityWanted

/-- **Mahler–Popken recurrence above the largest leaf value.** If $1 \le m < n$, the $m$-ary
complexity of $n$ is the minimum of the costs of splitting $n$ as a sum of two positive integers
or a product of two integers greater than one. The cost of a split is the sum of the $m$-ary
complexities of its two parts. The threshold comes from the leaves: every leaf has value at most
$m$, so a minimum-size expression for $n > m$ has a sum or a product at its root.

This sharpens Campbell's Proposition 1, which states the recursion (9) for all sufficiently
large $n$, to every $n > m$; for $m = 2$ it gives the binary case $n \ge 3$ stated there.

Source: John M. Campbell, "A Binary Version of the Mahler-Popken Complexity Function",
*INTEGERS* 24 (2024), Article A94, Proposition 1. -/
theorem mahlerPopkenComplexity_eq_recursionValue_of_lt {m n : ℕ} (hm : 1 ≤ m) (hn : m < n) :
    mahlerPopkenComplexity m n = mahlerPopkenRecursionValue m n := by
  have hn_one : 1 < n := by omega
  unfold mahlerPopkenRecursionValue
  apply le_antisymm
  · apply le_csInf
    · exact ⟨_, Or.inr ⟨1, Nat.one_pos, hn_one, rfl⟩⟩
    · rintro k (⟨d, hd, -, -, rfl⟩ | ⟨η, hη, hηn, rfl⟩)
      · have hn_pos : 0 < n := Nat.zero_lt_of_lt hn_one
        have hd_pos := Nat.pos_of_dvd_of_pos hd hn_pos
        have hq_pos := Nat.div_pos (Nat.le_of_dvd hn_pos hd) hd_pos
        have hprod : d * (n / d) = n := by rw [Nat.mul_comm, Nat.div_mul_cancel hd]
        simpa only [hprod] using mahlerPopkenComplexity_mul_le hm hd_pos hq_pos
      · have hsum : η + (n - η) = n := Nat.add_sub_of_le hηn.le
        simpa only [hsum] using mahlerPopkenComplexity_add_le hm hη (Nat.sub_pos_of_lt hηn)
  · obtain ⟨e, he, hc⟩ := mahlerPopkenComplexity_spec hm hn_one.le
    cases e with
    | leaf i =>
      simp only [MahlerPopkenExpr.eval_leaf] at he
      omega
    | add a b =>
      simp only [MahlerPopkenExpr.eval_add] at he
      simp only [MahlerPopkenExpr.count_add] at hc
      have ha := a.eval_pos
      have hb := b.eval_pos
      have hsub : n - a.eval = b.eval := by omega
      calc
        _ ≤ mahlerPopkenComplexity m a.eval + mahlerPopkenComplexity m b.eval := by
          apply Nat.sInf_le
          exact Or.inr ⟨a.eval, ha, by omega, by rw [hsub]⟩
        _ ≤ _ := hc ▸ Nat.add_le_add (mahlerPopkenComplexity_min_le a rfl)
          (mahlerPopkenComplexity_min_le b rfl)
    | mul a b =>
      simp only [MahlerPopkenExpr.eval_mul] at he
      simp only [MahlerPopkenExpr.count_mul] at hc
      have ha_cost := mahlerPopkenComplexity_min_le a rfl
      have hb_cost := mahlerPopkenComplexity_min_le b rfl
      -- Removing a factor of value one would strictly reduce the leaf count.
      have ha : a.eval ≠ 1 := by
        intro h
        rw [h, one_mul] at he
        rw [he] at hb_cost
        have := a.count_pos
        omega
      have hb : b.eval ≠ 1 := by
        intro h
        rw [h, mul_one] at he
        rw [he] at ha_cost
        have := b.count_pos
        omega
      have ha_lt : a.eval < n := by
        have hb_gt : 1 < b.eval := by
          have := b.eval_pos
          omega
        simpa only [Nat.mul_one, he] using Nat.mul_lt_mul_of_pos_left hb_gt a.eval_pos
      have hdiv : n / a.eval = b.eval := by rw [← he, Nat.mul_div_cancel_left _ a.eval_pos]
      calc
        _ ≤ mahlerPopkenComplexity m a.eval + mahlerPopkenComplexity m b.eval := by
          apply Nat.sInf_le
          exact Or.inl ⟨a.eval, ⟨b.eval, he.symm⟩, ha, ha_lt.ne, by rw [hdiv]⟩
        _ ≤ _ := hc ▸ Nat.add_le_add ha_cost hb_cost

/-- **The $m$-ary complexity eventually satisfies its recursion.** For every natural number
$m \ge 1$ there is $N$ such that for every $n \ge N$, the $m$-ary Mahler–Popken complexity
$\|n\|_m$ equals the right-hand side of the recursion (9), that is, the least of the values
$\|d\|_m + \|n/d\|_m$ over divisors $d$ of $n$ with $d \ne 1$ and $d \ne n$, and the values
$\|\eta\|_m + \|n - \eta\|_m$ over $0 < \eta < n$.

Source: John M. Campbell, "A Binary Version of the Mahler-Popken
Complexity Function", Proposition 1. -/
theorem mahlerPopkenComplexity_eq_recursionValue_eventually
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      mahlerPopkenComplexity m n = mahlerPopkenRecursionValue m n :=
  ⟨m + 1, fun _ hn ↦ mahlerPopkenComplexity_eq_recursionValue_of_lt hm hn⟩

end MathlibExt.NumberTheory.MahlerPopkenComplexityWanted

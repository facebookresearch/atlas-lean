/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Exponential
import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry12SummableSuccN

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 12

Summability of (n+k)^(r+k)/(aᵏk!) for |a|>e.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry12SummableRN

/-- **Absolute convergence of the series in Entry 12.** Let $r$ be an integer and let $n$ and $a$
be complex numbers. Suppose that $|a| > e$, or that $a = e$ and $r \le -2$, and that $n + k \ne 0$
for every natural number $k$ with $r + k < 0$. Then
$$\sum_{k=0}^{\infty} \left| \frac{(n+k)^{r+k}}{a^k\, k!} \right| < \infty.$$

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, definition (12.1) and Entry 12,
    printed pp. 66-67 / PDF pp. 76-77.
Proves `Wanted` entry `ramanujan_part1_ch3_entry12_summable_r_n`.
-/
theorem ramanujan_part1_ch3_entry12_summable_r_n (r : ℤ)
    (n a : ℂ)
        (ha : ‖a‖ > Real.exp 1 ∨ (a = (Real.exp 1 : ℂ) ∧ r ≤ -2))
            (hn : ∀ k : ℕ, r + (k : ℤ) < 0 → n + (k : ℂ) ≠ 0) :
    Summable (fun k : ℕ => ‖(n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (Nat.factorial k : ℂ))‖) := by
  have h := Entry12SummableSuccN.ramanujan_part1_ch3_entry12_summable_succ_n_general (r - 1) n a
      (ha.imp_right fun h => ⟨h.1, by omega⟩)
  simpa only [sub_add_cancel] using h

end Entry12SummableRN

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3

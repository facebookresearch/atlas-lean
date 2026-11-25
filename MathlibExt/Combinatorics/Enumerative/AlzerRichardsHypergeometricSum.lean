/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Binomial
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.LinearCombination

/-!
# The Alzer–Richards binomial sum as a hypergeometric series

Pairing consecutive factors in a falling factorial gives the two upper Pochhammer
factors in the terminating hypergeometric expression for the Alzer–Richards sum.
-/

namespace MetaMathlibExt

open Finset Polynomial

namespace sum_choose_mul_choose_div_choose_eq_hypergeometric3F2

private lemma choose_eq_rising_div (z : ℂ) (k : ℕ) :
    Ring.choose z k = (ascPochhammer ℂ k).eval (z - k + 1) / k.factorial := by
  rw [Ring.choose_eq_smul, descPochhammer_smeval_eq_ascPochhammer,
    ascPochhammer_smeval_eq_eval, smul_eq_mul, div_eq_inv_mul]

-- Each pair of factors in the falling factorial contributes one factor at each half-argument.
private lemma paired_factors (z : ℂ) (k : ℕ) :
    (descPochhammer ℂ (2 * k)).eval z = 2 ^ (2 * k) *
      ((ascPochhammer ℂ k).eval (-z / 2) * (ascPochhammer ℂ k).eval ((1 - z) / 2)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, descPochhammer_succ_eval,
      descPochhammer_succ_eval, ih, ascPochhammer_succ_eval, ascPochhammer_succ_eval,
      pow_succ, pow_succ]
    push_cast
    ring

private lemma half_product {m k : ℕ} (hk : 2 * k ≤ m) :
    (ascPochhammer ℂ k).eval (-(m : ℂ) / 2) * (ascPochhammer ℂ k).eval ((1 - (m : ℂ)) / 2) =
      (m.factorial : ℂ) / (2 ^ (2 * k) * (m - 2 * k).factorial) := by
  have hf : ((m - 2 * k).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  apply (eq_div_iff (mul_ne_zero (pow_ne_zero _ (by norm_num)) hf)).2
  calc
    _ = ((m - 2 * k).factorial : ℂ) * (descPochhammer ℂ (2 * k)).eval (m : ℂ) := by
      rw [paired_factors]
      ring
    _ = _ := by
      rw [descPochhammer_eval_eq_descFactorial, ← Nat.cast_mul, Nat.factorial_mul_descFactorial hk]

private lemma rising_ne_zero {z : ℂ} {k N : ℕ} (hk : k ≤ N)
    (hz : ∀ j : ℕ, 1 ≤ j → j ≤ N → z ≠ -j) : (ascPochhammer ℂ k).eval (z + 1) ≠ 0 := by
  intro h
  obtain ⟨i, hi, he⟩ := (ascPochhammer_eval_eq_zero_iff _ _).mp h
  apply hz (i + 1) (by omega) (by omega)
  push_cast
  linear_combination he

end sum_choose_mul_choose_div_choose_eq_hypergeometric3F2

open sum_choose_mul_choose_div_choose_eq_hypergeometric3F2 in
/-- **The Alzer–Richards binomial sum as a ${}_3F_2$ series.** Let $m \ge 1$ be an integer and
let $p, x$ be complex numbers with $p \ne -j$ and $x \ne -j$ for every integer $j$ with
$1 \le j \le \lfloor m/2 \rfloor$. Write $\binom{z}{k} = z(z-1)\cdots(z-k+1)/k!$ for complex $z$
and $(z)_n = z(z+1)\cdots(z+n-1)$ for the rising factorial. Then
$$
\sum_{k=0}^{\lfloor m/2 \rfloor} \frac{\binom{m-k}{k} \binom{m+x}{m-k}}{2^{2k} \binom{k+p}{k}} =
\frac{(x+1)_m}{m!} \sum_{n=0}^{\lfloor m/2 \rfloor}
\frac{(-m/2)_n \, ((1-m)/2)_n}{(p+1)_n \, (x+1)_n}.
$$

The sum on the right is the terminating hypergeometric series
${}_3F_2(-m/2, (1-m)/2, 1; p+1, x+1; 1)$, written out up to $n = \lfloor m/2 \rfloor$, beyond
which its terms vanish.

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 9 (i), Equation (15). -/
public theorem sum_choose_mul_choose_div_choose_eq_hypergeometric3F2 {m : ℕ} (hm : 1 ≤ m)
    {p x : ℂ} (hp : ∀ j : ℕ, 1 ≤ j → j ≤ m / 2 → p ≠ -j)
    (hx : ∀ j : ℕ, 1 ≤ j → j ≤ m / 2 → x ≠ -j) :
    ∑ k ∈ range (m / 2 + 1), ((m - k).choose k : ℂ) * Ring.choose ((m : ℂ) + x) (m - k) /
        (2 ^ (2 * k) * Ring.choose ((k : ℂ) + p) k) =
      (ascPochhammer ℂ m).eval (x + 1) / (m.factorial : ℂ) *
        ∑ n ∈ range (m / 2 + 1), (ascPochhammer ℂ n).eval (-(m : ℂ) / 2) *
          (ascPochhammer ℂ n).eval ((1 - (m : ℂ)) / 2) /
            ((ascPochhammer ℂ n).eval (p + 1) * (ascPochhammer ℂ n).eval (x + 1)) := by
  rw [mul_sum]
  apply sum_congr rfl
  intro k hmem
  have hk : k ≤ m / 2 := Nat.le_of_lt_succ (mem_range.mp hmem)
  have hkm : k ≤ m := (hk.trans_lt (Nat.div_lt_self hm (by decide))).le
  have hsplit := congrArg (eval (x + 1)) (ascPochhammer_mul ℂ k (m - k))
  simp only [eval_mul, eval_comp, eval_add, eval_X, eval_natCast, Nat.add_sub_of_le hkm] at hsplit
  rw [Nat.cast_choose ℂ (show k ≤ m - k by omega), choose_eq_rising_div, choose_eq_rising_div,
    Nat.cast_sub hkm, show (m : ℂ) + x - (m - k) + 1 = x + 1 + k by ring,
    show (k : ℂ) + p - k + 1 = p + 1 by ring, ← hsplit, half_product (by omega : 2 * k ≤ m),
    show m - k - k = m - 2 * k by omega]
  have hf (r : ℕ) : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  field_simp [hf, rising_ne_zero hk hp, rising_ne_zero hk hx]

end MetaMathlibExt

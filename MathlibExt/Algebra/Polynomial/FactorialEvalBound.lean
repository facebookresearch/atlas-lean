/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Choose.Sum

/-!
# A lower bound for integer polynomial values

The top forward difference is the leading coefficient times the degree factorial.
Its expansion as an alternating binomial sum bounds it in terms of the largest sampled value.
-/

open Finset Polynomial

namespace MetaMathlibExt

/-- **Integer polynomials take a large value at a small nonnegative integer.** Let
$f \in \mathbb{Z}[x]$ have degree $d$. Then there is an integer $x$ with $0 \le x \le d$ such that
$|f(x)| \ge d!/2^d$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 5 (`integers-2025-A41-lem-5`). -/
public theorem exists_factorial_div_two_pow_le_abs_eval (f : ℤ[X]) (d : ℕ)
    (hf : f.degree = d) :
    ∃ x ∈ Finset.range (d + 1), (d.factorial : ℚ) / 2 ^ d ≤ |((f.eval (x : ℤ) : ℤ) : ℚ)| := by
  have hne : f ≠ 0 := degree_ne_bot.mp (hf ▸ WithBot.coe_ne_bot)
  have hdiff := congrFun f.fwdDiff_iter_degree_eq_factorial 0
  rw [natDegree_eq_of_degree_eq_some hf, fwdDiff_iter_eq_sum_shift] at hdiff
  obtain ⟨x, hx, hmax⟩ := (range (d + 1)).exists_max_image (fun k : ℕ ↦ |f.eval (k : ℤ)|)
    nonempty_range_add_one
  refine ⟨x, hx, (div_le_iff₀ (by positivity)).mpr ?_⟩
  have hbound : (d.factorial : ℤ) ≤ |f.eval (x : ℤ)| * 2 ^ d := calc
    (d.factorial : ℤ) ≤ |f.leadingCoeff| * d.factorial :=
      le_mul_of_one_le_left (by positivity) (Int.one_le_abs (leadingCoeff_ne_zero.mpr hne))
    _ = |∑ k ∈ range (d + 1), (-1 : ℤ) ^ (d - k) * d.choose k * f.eval (k : ℤ)| := by
      simpa [abs_mul, zsmul_eq_mul] using congrArg abs hdiff.symm
    _ ≤ ∑ k ∈ range (d + 1), |(-1 : ℤ) ^ (d - k) * d.choose k * f.eval (k : ℤ)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range (d + 1), |f.eval (x : ℤ)| * d.choose k := by
      apply sum_le_sum
      intro k hk
      simpa [abs_mul, abs_pow, mul_comm] using
        mul_le_mul_of_nonneg_right (hmax k hk) (Int.natCast_nonneg (d.choose k))
    _ = |f.eval (x : ℤ)| * 2 ^ d := by
      rw [← mul_sum]
      exact congrArg (|f.eval (x : ℤ)| * ·) (by exact_mod_cast Nat.sum_range_choose d)
  exact_mod_cast hbound

end MetaMathlibExt

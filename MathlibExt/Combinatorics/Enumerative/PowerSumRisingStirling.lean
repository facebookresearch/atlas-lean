/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.Ring

/-!
# Power sums via the rising factorial basis

## References

* Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
  INTEGERS 24 (2024), Article A70, pp. 1–31, Corollary 5, Equation (4.4).
* R. L. Graham, D. E. Knuth, and O. Patashnik, *Concrete Mathematics: A Foundation for
  Computer Science*, Addison-Wesley, 1989, §6.1, Identity (6.12), and the table on p. 174,
  cited by Parisse for the rising-factorial expansion (4.3) and binomial summation (2.4),
  respectively.
-/

namespace MetaMathlibExt

open Finset Polynomial

private theorem pow_eq_sum_descPochhammer (x : ℤ) (m : ℕ) :
    x ^ m = ∑ j ∈ range (m + 1), (Nat.stirlingSecond m j : ℤ) * (descPochhammer ℤ j).eval x := by
  -- The polynomial identity follows from Mathlib's expansion at every natural number.
  have h : (X : ℤ[X]) ^ m =
      ∑ j ∈ range (m + 1), (Nat.stirlingSecond m j : ℤ[X]) * descPochhammer ℤ j := by
    apply eq_of_infinite_eval_eq
    refine (Set.infinite_range_of_injective Int.ofNat_injective).mono ?_
    rintro _ ⟨k, rfl⟩
    change ((X : ℤ[X]) ^ m).eval (k : ℤ) = eval (k : ℤ) _
    simpa only [eval_pow, eval_X, eval_finsetSum, eval_natCast_mul,
      descPochhammer_eval_eq_descFactorial, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow] using
      congrArg (fun t : ℕ => (t : ℤ)) (Nat.pow_eq_sum_stirlingSecond_mul_descFactorial k m)
  simpa only [eval_pow, eval_X, eval_finsetSum, eval_natCast_mul] using congrArg (eval x) h

private theorem pow_eq_sum_rising (k m : ℕ) :
    (k : ℤ) ^ m = ∑ j ∈ range (m + 1),
      (-1) ^ (m - j) * (j.factorial : ℤ) * (Nat.stirlingSecond m j : ℤ) *
        ((k + j - 1).choose j : ℤ) := by
  calc
    (k : ℤ) ^ m = (-1) ^ m * (-(k : ℤ)) ^ m := by rw [← mul_pow]; simp
    _ = _ := by
      rw [pow_eq_sum_descPochhammer (-(k : ℤ)) m, mul_sum]
      refine sum_congr rfl fun j hj => ?_
      have hsign : (-1 : ℤ) ^ m = (-1) ^ (m - j) * (-1) ^ j := by
        rw [← pow_add, Nat.sub_add_cancel (Nat.lt_succ_iff.mp (mem_range.mp hj))]
      calc
        _ = (-1) ^ (m - j) * (Nat.stirlingSecond m j : ℤ) *
            ((-1) ^ j * (descPochhammer ℤ j).eval (-(k : ℤ))) := by
          rw [hsign]
          ac_rfl
        _ = _ := by
          rw [← ascPochhammer_eval_neg_eq_descPochhammer, neg_neg,
            ascPochhammer_nat_eq_natCast_ascFactorial, Nat.ascFactorial_eq_factorial_mul_choose',
            Nat.cast_mul]
          ring

private theorem sum_Icc_choose_shift (n j : ℕ) :
    ∑ k ∈ Icc 1 n, (k + j - 1).choose j = (n + j).choose (j + 1) := by
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  simp only [show ∀ k : ℕ, 1 + k + j - 1 = k + j by omega]
  cases n with
  | zero => simp
  | succ n => simpa only [Nat.succ_add] using Nat.sum_range_add_choose n j

/-- **Sums of $m$th powers via Stirling numbers of the second kind.** For all natural numbers
$n$ and $m$,
$$\sum_{k=1}^{n} k^m = \sum_{k=0}^{m} (-1)^{m-k}\, k!\, \binom{n + k}{k + 1}\, S(m, k),$$
where $S(m, k)$ denotes the Stirling numbers of the second kind.

The paper takes $n \ge 1$; for $n = 0$ both sides vanish, so that case is included.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Corollary 5, Equation (4.4) (`integers-2024-A70-cor-5`). -/
public theorem sum_pow_eq_sum_stirlingSecond (n m : ℕ) :
    ∑ k ∈ Icc 1 n, (k : ℤ) ^ m =
      ∑ k ∈ range (m + 1),
        (-1) ^ (m - k) * (k.factorial : ℤ) * ((n + k).choose (k + 1) : ℤ) *
          (Nat.stirlingSecond m k : ℤ) := by
  simp_rw [pow_eq_sum_rising]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [← mul_sum, ← Nat.cast_sum, sum_Icc_choose_shift]
  ring

end MetaMathlibExt

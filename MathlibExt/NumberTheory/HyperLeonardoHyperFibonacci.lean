/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.HyperLeonardo
import Mathlib.Data.Nat.Choose.Sum
import all MathlibExt.NumberTheory.GenLeonardo

/-!
# Hyper-Leonardo numbers in terms of hyper-Fibonacci numbers

## References

* Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino,
  *A Note on Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, pp. 1–18,
  Proposition 6, Equation (9).
* Efruz Özlem Mersin and Mustafa Bahşi, *Hyper-Leonardo Numbers*, Conference Proceedings of
  Science and Technology 5 (2022), no. 1, pp. 14–20, Theorem 5(i), the original identity.
* Paula Catarino and Ana Borges, *On Leonardo numbers*, Acta Mathematica Universitatis
  Comenianae 89 (2020), no. 1, pp. 75–86, Proposition 2.2, the order-zero identity.
* Ayhan Dil and István Mező, *A symmetric algorithm for hyperharmonic and Fibonacci numbers*,
  Applied Mathematics and Computation 206 (2008), no. 2, pp. 942–951, Section 4.3.2,
  the definition of the hyper-Fibonacci numbers.
-/

namespace MetaMathlibExt

/-- **Hyper-Leonardo numbers in terms of hyper-Fibonacci numbers.** For all natural numbers $r$
and $n$, the hyper-Leonardo number $\mathrm{Le}^{(r)}_n$ and the hyper-Fibonacci number
$F^{(r)}_{n+1}$ satisfy $\mathrm{Le}^{(r)}_n = 2F^{(r)}_{n+1} - \binom{n+r}{r}$ as integers.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 6, Equation (9)
(`integers-2026-A48-prop-6`). -/
public theorem hyperLeonardo_eq_hyperFibonacci (r n : ℕ) :
    hyperLeonardo r n = 2 * (hyperFibonacci r (n + 1) : ℤ) - ((n + r).choose r : ℕ) := by
  have hzero (s : ℕ) : hyperFibonacci s 0 = 0 := by
    induction s with
    | zero => rw [hyperFibonacci_zero, Nat.fib_zero]
    | succ s ih => simpa only [hyperFibonacci_succ, Nat.zero_add, Finset.sum_range_one] using ih
  induction r generalizing n with
  | zero =>
    simp only [hyperLeonardo_zero, hyperFibonacci_zero, Nat.choose_zero_right, Nat.cast_one]
    have h := genLeonardo_add_eq_mul_fib 1 n
    omega
  | succ r ih =>
    rw [hyperLeonardo_succ, hyperFibonacci_succ, Nat.cast_sum,
      Finset.sum_range_succ' (fun k => (hyperFibonacci r k : ℤ)), hzero r, Nat.cast_zero, add_zero]
    simp_rw [ih]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [← Nat.cast_sum, Nat.sum_range_add_choose, Nat.add_assoc]

end MetaMathlibExt

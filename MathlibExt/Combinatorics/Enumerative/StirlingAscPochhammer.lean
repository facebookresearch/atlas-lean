/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Stirling numbers of the first kind and the rising factorial

The unsigned Stirling numbers of the first kind `Nat.stirlingFirst n k` are the coefficients of
the rising factorial `x^{(n)} = x (x + 1) ⋯ (x + n - 1)` (`ascPochhammer`):

`x^{(n)} = ∑_{k=0}^{n} stirlingFirst n k * x ^ k`.

## Main results

* `Nat.sum_stirlingFirst_mul_X_pow`: the polynomial identity in `S[X]`.
* `Nat.sum_stirlingFirst_mul_pow`: its evaluation at any `x` in a semiring.

## References

* R. L. Graham, D. E. Knuth, O. Patashnik, *Concrete Mathematics*, 2nd ed. (1994), §6.1.
-/

@[expose] public section

open Finset Polynomial

namespace Nat

/-- The rising factorial is the generating polynomial of the unsigned Stirling numbers of the
first kind: `ascPochhammer S n = ∑_{k=0}^{n} stirlingFirst n k * X ^ k`
(Graham–Knuth–Patashnik, §6.1). -/
theorem sum_stirlingFirst_mul_X_pow (S : Type*) [Semiring S] (n : ℕ) :
    ∑ k ∈ range (n + 1), (stirlingFirst n k : S[X]) * X ^ k = ascPochhammer S n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_right, ← ih, sum_range_succ', stirlingFirst_succ_zero,
      Nat.cast_zero, zero_mul, add_zero]
    simp only [stirlingFirst_succ_succ, Nat.cast_add, Nat.cast_mul, add_mul, sum_add_distrib]
    rw [mul_add, sum_mul, sum_mul]
    have h1 : ∑ k ∈ range (n + 1), ((n : S[X]) * (stirlingFirst n (k + 1) : S[X])) * X ^ (k + 1)
        = ∑ k ∈ range (n + 1), (stirlingFirst n k : S[X]) * X ^ k * (n : S[X]) := by
      rw [sum_range_succ, stirlingFirst_eq_zero_of_lt (Nat.lt_succ_self n), sum_range_succ' _ n]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [stirlingFirst_succ_zero]
        simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
        refine sum_congr rfl fun k _ => ?_
        rw [mul_assoc, (Nat.cast_commute (m + 1) _).eq]
    have h2 : ∑ k ∈ range (n + 1), (stirlingFirst n k : S[X]) * X ^ (k + 1)
        = ∑ k ∈ range (n + 1), (stirlingFirst n k : S[X]) * X ^ k * X := by
      refine sum_congr rfl fun k _ => ?_
      rw [pow_succ, mul_assoc]
    rw [h1, h2, add_comm]

/-- **Stirling numbers of the first kind and the rising factorial**:
`∑_{k=0}^{n} stirlingFirst n k * x ^ k = x (x + 1) ⋯ (x + n - 1)`
(Graham–Knuth–Patashnik, §6.1). -/
theorem sum_stirlingFirst_mul_pow {S : Type*} [Semiring S] (n : ℕ) (x : S) :
    ∑ k ∈ range (n + 1), (stirlingFirst n k : S) * x ^ k = (ascPochhammer S n).eval x := by
  rw [← sum_stirlingFirst_mul_X_pow, eval_finsetSum]
  simp only [eval_natCast_mul, eval_X_pow]

end Nat

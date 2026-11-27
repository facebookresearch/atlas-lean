/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Tactic.Ring

/-!
# Lee's factorial-weighted alternating row sum

The Stirling recurrence expresses the difference between two consecutive weighted rows
as a telescoping sum. Its boundary terms come from the one-block partition and the
vanishing of Stirling numbers above the diagonal.
-/

open Finset

namespace MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted

/-- **Lee's factorial-weighted alternating row sum of Stirling numbers of the second kind.** Write
$S(a, j)$ for the Stirling number of the second kind, the number of partitions of an $a$-element
set into $j$ nonempty blocks. For every natural number $a \ge 1$, the following identity of
integers holds:
$$\sum_{j=2}^{a} (-1)^j\, (j-2)!\, S(a, j) = a - 1.$$

Source: Kwankyu Lee, "Some New Identities for Stirling Numbers", Lemma 6
(TeX label `lem:mjkfwd`). -/
public theorem sum_stirlingSecond_factorial_alternating
    {a : ℕ} (ha : 1 ≤ a) :
    (∑ j ∈ Finset.Icc 2 a,
      (Nat.stirlingSecond a j : ℤ) * (Nat.factorial (j - 2) : ℤ) *
        (-1 : ℤ) ^ j) = (a : ℤ) - 1 := by
  let term (n j : ℕ) : ℤ :=
    (Nat.stirlingSecond n j : ℤ) * (j - 2).factorial * (-1) ^ j
  change ∑ j ∈ Icc 2 a, term a j = (a : ℤ) - 1
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  clear ha
  induction n with
  | zero => decide
  | succ n ih =>
    let boundary (j : ℕ) : ℤ :=
      (Nat.stirlingSecond (n + 1) (j - 1) : ℤ) * (j - 2).factorial * (-1) ^ j
    calc
      _ = ∑ j ∈ Icc 2 (n + 2), (term (n + 1) j - (boundary (j + 1) - boundary j)) := by
        apply sum_congr rfl
        intro j hj
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (mem_Icc.mp hj).1
        simp only [term, boundary, Nat.stirlingSecond_succ_succ (n + 1), Nat.cast_add,
          Nat.cast_mul, Nat.add_sub_cancel, Nat.succ_sub_one,
          show k + 2 + 1 - 2 = k + 1 by omega,
          Nat.factorial_succ k, Nat.cast_succ, pow_succ (-1 : ℤ) (k + 2)]
        ring
      _ = _ := by
        rw [sum_sub_distrib, sum_Icc_sub (by omega), sum_Icc_succ_top (by omega), ih]
        simp [term, boundary, Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self (n + 1)),
          Nat.stirlingSecond_one_right]

end MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted

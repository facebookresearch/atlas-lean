/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import MathlibExt.Combinatorics.DixonCubicBinomial
import MathlibExt.NumberTheory.Recurrences.LucasSequenceAddition

/-!
# Dixon-type alternating binomial sum with Lucas sequences

Reflecting `k` to `2n - k` preserves the alternating cubic binomial weight. The Lucas addition
formula reduces the paired products to a constant, leaving Dixon's scalar sum.

## References

* John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
  Sequences*, The Fibonacci Quarterly 62 (2024), no. 1, 57–64, Theorem 2.2 (Lucas sum) and
  equation (1.12) (scalar sum).
* A. C. Dixon, *On the sum of the cubes of the coefficients in a certain expansion by the binomial
  theorem*, Messenger of Mathematics 20 (1891), 79–80 (scalar sum).
* Vladimir V. Kruchinin and Maria Y. Perminova, *Identities and Hadamard Product of the Generalized
  Fibonacci, Lucas, Catalan, and Harmonic Numbers*, Journal of Integer Sequences 28 (2025),
  Article 25.8.8, 1–17, Proposition 1 (Lucas addition formula).
-/

namespace MetaMathlibExt

open Finset
open MathlibExt.NumberTheory.Recurrences.KruchininPerminovaHadamardWanted (two_mul_lucasU_add)

set_option backward.proofsInPublic true in
/-- **Dixon-type alternating sum with Lucas sequences.** Let $p$ be an integer and let $U_n$ and
$V_n$ be the Lucas sequences $U(p, -1)$ and $V(p, -1)$, so $U_0 = 0$, $U_1 = 1$, $V_0 = 2$,
$V_1 = p$ and both satisfy $X_{j+2} = p X_{j+1} + X_j$. Then for every natural number $n$,
$$\sum_{k=0}^{2n} (-1)^k \binom{2n}{k}^3 U_{2n-k} V_k = (-1)^n \binom{3n}{n} \binom{2n}{n} U_{2n},$$
where $\binom{3n}{n} \binom{2n}{n} = (3n)!/(n!)^3$ is the trinomial coefficient.

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023, Theorem 2.2. -/
public theorem lucasU_lucasV_sum_choose_cube_alternating (p : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n + 1),
        ((2 * n).choose k : ℤ) ^ 3 * (-1) ^ k *
          lucasU ⟨p, -1, by decide⟩ (2 * n - k) * lucasV ⟨p, -1, by decide⟩ k =
      (-1) ^ n * ((3 * n).choose n * (2 * n).choose n : ℕ) * lucasU ⟨p, -1, by decide⟩ (2 * n) := by
  let P : LucasSequenceParams := ⟨p, -1, by decide⟩
  let a (k : ℕ) : ℤ := ((2 * n).choose k : ℤ) ^ 3 * (-1) ^ k
  have hsymm (k : ℕ) (hk : k ≤ 2 * n) : a (2 * n - k) = a k := by
    have hsign : (-1 : ℤ) ^ (2 * n - k) = (-1) ^ k := by
      apply mul_right_cancel₀ (pow_ne_zero k (neg_ne_zero.mpr one_ne_zero))
      rw [← pow_add, ← pow_add, Nat.sub_add_cancel hk, ← two_mul k]
      simp only [pow_mul, neg_one_sq, one_pow]
    simp only [a, Nat.choose_symm hk, hsign]
  have hrefl :
      ∑ k ∈ range (2 * n + 1), a k * lucasV P (2 * n - k) * lucasU P k =
        ∑ k ∈ range (2 * n + 1), a k * lucasU P (2 * n - k) * lucasV P k := by
    rw [← sum_range_reflect]
    refine sum_congr rfl fun k hk => ?_
    have hkn := mem_range_succ_iff.mp hk
    rw [Nat.add_sub_cancel, Nat.sub_sub_self hkn, hsymm k hkn]
    ac_rfl
  have hdixon : ∑ k ∈ range (2 * n + 1), a k =
      (-1 : ℤ) ^ n * ((3 * n).choose n * (2 * n).choose n : ℕ) := by
    have hchoose : (3 * n).choose (2 * n) = (3 * n).choose n := by
      have hn : n ≤ 3 * n := by omega
      simpa only [show 3 * n - n = 2 * n by omega] using (Nat.choose_symm hn)
    have hd := dixon_alternating_cubic_binomial_sum n
    rw [hchoose] at hd
    simpa only [a, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hd
  change (∑ k ∈ range (2 * n + 1), a k * lucasU P (2 * n - k) * lucasV P k) = _
  apply mul_left_cancel₀ (two_ne_zero (α := ℤ))
  calc
    2 * (∑ k ∈ range (2 * n + 1), a k * lucasU P (2 * n - k) * lucasV P k) =
        ∑ k ∈ range (2 * n + 1), a k *
          (lucasU P (2 * n - k) * lucasV P k + lucasV P (2 * n - k) * lucasU P k) := by
      rw [two_mul]
      simp only [mul_add, ← mul_assoc, sum_add_distrib, hrefl]
    _ = ∑ k ∈ range (2 * n + 1), a k * (2 * lucasU P (2 * n)) := by
      refine sum_congr rfl fun k hk => ?_
      rw [← two_mul_lucasU_add, Nat.sub_add_cancel (mem_range_succ_iff.mp hk)]
    _ = _ := by
      rw [← sum_mul, hdixon]
      ac_rfl

end MetaMathlibExt

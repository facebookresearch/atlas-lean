/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.Recurrences.LucasSequenceAddition

/-!
# Alternating squared-binomial sum with Lucas sequences

This module proves `MetaMathlibExt.lucasU_lucasV_sum_choose_sq_alternating`: for every integer
`p` and every natural number `n`,
`∑_{k=0}^{2n} (-1)^k C(2n, k)^2 U_{2n-k} V_k = (-1)^n C(2n, n) U_{2n}`,
where `U` and `V` are the Lucas sequences `U(p, -1)` and `V(p, -1)`.

By the same reflection argument, the unsigned weights `C(n, k)^2` reduce
`MetaMathlibExt.lucasU_lucasV_sum_choose_sq` to Vandermonde's identity.

The statements are from John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order
Linearly Recurrent Sequences*, The Fibonacci Quarterly 62 (2024), no. 1, 57–64. The paper's
sequences `U_0 = 0`, `U_1 = 1`, `V_0 = 2`, `V_1 = p`, `X_n = p X_{n-1} + X_{n-2}` are the Lucas
sequences `U(p, -1)` and `V(p, -1)`, written `lucasU ⟨p, -1, _⟩` and `lucasV ⟨p, -1, _⟩`. The
paper leaves the parameter `p` unrestricted; the statement takes `p` an arbitrary integer.

## Proof

The weights `a_k = (-1)^k C(2n, k)^2` are symmetric under `k ↦ 2n - k`. Reflecting the sum and
adding it to itself gives `∑_k a_k (U_{2n-k} V_k + V_{2n-k} U_k)`, and each bracket is `2 U_{2n}`
by the addition formula `2 U_{m+n} = U_m V_n + V_m U_n` of
`MathlibExt.NumberTheory.Recurrences.LucasSequenceAddition`. It remains to evaluate
`∑_k (-1)^k C(2n, k)^2 = (-1)^n C(2n, n)`, the coefficient of `X^{2n}` in
`(X + 1)^{2n} (X - 1)^{2n} = (X^2 - 1)^{2n}`.

## References

* John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
  Sequences*, The Fibonacci Quarterly 62 (2024), no. 1, 57–64, Theorem 2.1 and Proposition 2.3.
* Vladimir V. Kruchinin and Maria Y. Perminova, *Identities and Hadamard Product of the Generalized
  Fibonacci, Lucas, Catalan, and Harmonic Numbers*, Journal of Integer Sequences 28 (2025),
  Article 25.8.8, 1–17, Proposition 1 (Lucas addition) and Theorem 2 (symmetric weights).
-/

namespace MetaMathlibExt

namespace lucasU_lucasV_sum_choose_sq_alternating

open Finset Polynomial

/-- For `k ≤ 2n`, the signs `(-1)^(2n - k)` and `(-1)^k` agree. -/
private theorem neg_one_pow_two_mul_sub {n k : ℕ} (hk : k ≤ 2 * n) :
    (-1 : ℤ) ^ (2 * n - k) = (-1) ^ k := by
  have h1 : (-1 : ℤ) ^ (2 * n - k) * (-1) ^ k = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hk, pow_mul, neg_one_sq, one_pow]
  have h2 : (-1 : ℤ) ^ k * (-1) ^ k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  linear_combination (-1 : ℤ) ^ k * h1 - (-1 : ℤ) ^ (2 * n - k) * h2

/-- The alternating sum of the squared binomial coefficients `C(2n, k)` is `(-1)^n C(2n, n)`:
compare the coefficients of `X^(2n)` in `(X + 1)^(2n) (X - 1)^(2n) = (X^2 - 1)^(2n)`. -/
private theorem sum_choose_sq_mul_neg_one_pow (n : ℕ) :
    ∑ k ∈ range (2 * n + 1), ((2 * n).choose k : ℤ) ^ 2 * (-1) ^ k =
      (-1) ^ n * ((2 * n).choose n : ℤ) := by
  have hprod : ((X + 1 : ℤ[X]) ^ (2 * n) * (X + C (-1)) ^ (2 * n)) =
      expand ℤ 2 ((X + C (-1)) ^ (2 * n)) := by
    rw [← mul_pow, map_pow, map_add, expand_X, expand_C]
    congr 1
    rw [C_neg, C_1]
    ring
  have hcoeff := congrArg (fun f : ℤ[X] => f.coeff (2 * n)) hprod
  rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, coeff_expand two_pos,
    ite_eq_left (dvd_mul_right 2 n), Nat.mul_div_cancel_left n two_pos, coeff_X_add_C_pow,
    show 2 * n - n = n by omega] at hcoeff
  rw [← hcoeff]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ 2 * n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [coeff_X_add_one_pow, coeff_X_add_C_pow, Nat.sub_sub_self hk', Nat.choose_symm hk']
  ring

end lucasU_lucasV_sum_choose_sq_alternating

open Finset in
open MathlibExt.NumberTheory.Recurrences.KruchininPerminovaHadamardWanted (two_mul_lucasU_add) in
/-- **Lucas convolution with symmetric weights.** Let $P,Q$ be integers with $Q \ne 0$, and let
$U = U(P,Q)$ and $V = V(P,Q)$ be the associated Lucas sequences. For a natural number $m$ and
integer weights $a_k$ satisfying $a_{m-k}=a_k$ for every $0\le k\le m$,

$$\sum_{k=0}^{m} a_k U_{m-k} V_k = \left(\sum_{k=0}^{m} a_k\right) U_m.$$ -/
public theorem sum_mul_lucasU_mul_lucasV_of_symm (P : LucasSequenceParams) (m : ℕ)
    (a : ℕ → ℤ) (ha : ∀ k ≤ m, a (m - k) = a k) :
    ∑ k ∈ range (m + 1), a k * lucasU P (m - k) * lucasV P k =
      (∑ k ∈ range (m + 1), a k) * lucasU P m := by
  apply mul_left_cancel₀ (two_ne_zero (α := ℤ))
  have hrefl : ∑ k ∈ range (m + 1), a k * lucasU P (m - k) * lucasV P k =
      ∑ k ∈ range (m + 1), a k * lucasV P (m - k) * lucasU P k := by
    rw [← sum_range_reflect]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [show m + 1 - 1 - k = m - k by omega, Nat.sub_sub_self hk', ha k hk']
    ring
  calc 2 * ∑ k ∈ range (m + 1), a k * lucasU P (m - k) * lucasV P k
      = ∑ k ∈ range (m + 1), a k * lucasU P (m - k) * lucasV P k +
          ∑ k ∈ range (m + 1), a k * lucasV P (m - k) * lucasU P k := by
        rw [two_mul, hrefl]
    _ = ∑ k ∈ range (m + 1), a k * (2 * lucasU P m) := by
        rw [← sum_add_distrib]
        refine sum_congr rfl fun k hk => ?_
        have h := two_mul_lucasU_add P (m - k) k
        rw [Nat.sub_add_cancel (Nat.lt_succ_iff.mp (mem_range.mp hk))] at h
        rw [h]
        ring
    _ = 2 * ((∑ k ∈ range (m + 1), a k) * lucasU P m) := by
        rw [← sum_mul]
        ring

-- Keep the nonzero proofs in the Lucas parameters inline, as in the wanted statement.
set_option backward.proofsInPublic true in
open lucasU_lucasV_sum_choose_sq_alternating in
/-- **Alternating squared-binomial sum with Lucas sequences.** Let $p$ be an integer and let
$U_n$ and $V_n$ be the Lucas sequences $U(p, -1)$ and $V(p, -1)$, so $U_0 = 0$, $U_1 = 1$,
$V_0 = 2$, $V_1 = p$ and both satisfy $X_{j+2} = p X_{j+1} + X_j$. Then for every natural
number $n$,
$$\sum_{k=0}^{2n} (-1)^k \binom{2n}{k}^2 U_{2n-k} V_k = (-1)^n \binom{2n}{n} U_{2n}.$$

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023, Theorem 2.1. -/
public theorem lucasU_lucasV_sum_choose_sq_alternating (p : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n + 1),
        ((2 * n).choose k : ℤ) ^ 2 * (-1) ^ k *
          lucasU ⟨p, -1, by decide⟩ (2 * n - k) * lucasV ⟨p, -1, by decide⟩ k =
      (-1) ^ n * ((2 * n).choose n : ℤ) * lucasU ⟨p, -1, by decide⟩ (2 * n) := by
  rw [sum_mul_lucasU_mul_lucasV_of_symm _ (2 * n)
      (fun k => ((2 * n).choose k : ℤ) ^ 2 * (-1) ^ k) ?_, sum_choose_sq_mul_neg_one_pow]
  intro k hk
  simp only [Nat.choose_symm hk, neg_one_pow_two_mul_sub hk]

set_option backward.proofsInPublic true in
/-- **Squared-binomial convolution of the Lucas sequences U and V.** Let $p$ be an integer and let
$U$ and $V$ be the Lucas sequences $U(p, -1)$ and $V(p, -1)$, so that $U_0 = 0$, $U_1 = 1$,
$V_0 = 2$, $V_1 = p$, and both satisfy $X_{j+2} = p X_{j+1} + X_j$. Then for every natural
number $n$
$$\sum_{k=0}^{n} \binom{n}{k}^2 U_{n-k} V_k = \binom{2n}{n} U_n.$$

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023, Proposition 2.3. -/
public theorem lucasU_lucasV_sum_choose_sq (p : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℤ) ^ 2 * lucasU ⟨p, -1, by decide⟩ (n - k) * lucasV ⟨p, -1, by decide⟩ k =
      ((2 * n).choose n : ℤ) * lucasU ⟨p, -1, by decide⟩ n := by
  have hchoose : ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) ^ 2 = ((2 * n).choose n : ℤ) := by
    exact_mod_cast Nat.sum_range_choose_sq n
  rw [sum_mul_lucasU_mul_lucasV_of_symm _ n (fun k => (n.choose k : ℤ) ^ 2) ?_, hchoose]
  intro k hk
  rw [Nat.choose_symm hk]

end MetaMathlibExt

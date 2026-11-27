/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.Coprime.Basic
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Divisibility of Lucas sums when `P = 1`

When $P = 1$, the sum $U_1 + cdots + U_n$ of a Lucas sequence is divisible by $n$
if and only if $U_{n+2} equiv 1 pmod n$, for positive $n$ coprime to $Q$.

Statements from Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of
Terms of Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36.
-/

namespace MetaMathlibExt

@[expose] public section

private theorem lucasU_sum_mul_q_of_p_eq_one (params : LucasSequenceParams)
    (hp : params.p = 1) (n : ℕ) :
    params.q * (∑ i ∈ Finset.Icc 1 n, lucasU params i) = 1 - lucasU params (n + 2) := by
  induction n with
  | zero =>
    simp [lucasU, hp]
  | succ n ih =>
    have hrec := lucasU_add_two params (n + 1)
    rw [hp] at hrec
    have e : (n + 1) + 1 = n + 2 := rfl
    rw [e] at hrec
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 n)]
    linear_combination ih + hrec

/-- **Divisibility of Lucas sums when $P = 1$.** Let $U$ be the Lucas sequence $U_0 = 0$,
$U_1 = 1$, $U_{j+2} = P U_{j+1} - Q U_j$ with $P = 1$ and $Q \ne 0$. For every positive integer
$n$ coprime to $Q$, $n \mid U_1 + \cdots + U_n$ if and only if $U_{n+2} \equiv 1 \pmod n$.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.6
(`integers-2024-A36-thm-2-6`). -/
public theorem lucasU_sum_dvd_iff_of_p_eq_one (params : LucasSequenceParams)
    (hp : params.p = 1) (n : ℕ) (hn : 0 < n) (hnb : IsCoprime (n : ℤ) params.q) :
    (n : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, lucasU params i ↔ lucasU params (n + 2) ≡ 1 [ZMOD n] := by
  have _ : 0 < n := hn
  have hkey := lucasU_sum_mul_q_of_p_eq_one params hp n
  rw [Int.modEq_iff_dvd]
  constructor
  · intro h
    have hq : (n : ℤ) ∣ params.q * (∑ i ∈ Finset.Icc 1 n, lucasU params i) :=
      h.mul_left _
    rw [hkey] at hq
    exact hq
  · intro h
    have hq : (n : ℤ) ∣ params.q * (∑ i ∈ Finset.Icc 1 n, lucasU params i) := by
      rw [hkey]; exact h
    exact hnb.dvd_of_dvd_mul_left hq

end

end MetaMathlibExt

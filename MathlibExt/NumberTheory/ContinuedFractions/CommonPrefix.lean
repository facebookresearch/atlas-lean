/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.ContinuedFractions.Computation.Approximations

/-!
# Real numbers with a common continued fraction prefix

Theorem `MetaMathlibExt.abs_sub_le_of_contFrac_prefix_eq` bounds the distance between two real
numbers by comparing both to the convergent determined by their common prefix.
-/

namespace MetaMathlibExt

open GenContFract
open GenContFract (of)

namespace abs_sub_le_of_contFrac_prefix_eq

private theorem convs_eq_of_prefix {x y : ℝ} {k : ℕ} (h : (of x).h = (of y).h)
    (hd : ∀ i < k, (of x).partDens.get? i = (of y).partDens.get? i) :
    (of x).convs k = (of y).convs k := by
  -- Each regular continued fraction coefficient is a pair with numerator one.
  have coeff (v : ℝ) (i : ℕ) : (of v).s.get? i =
      ((of v).partDens.get? i).map (fun b => (⟨1, b⟩ : Pair ℝ)) := by
    simp [partDens, GenContFract.of, IntFractPair.seq1, Option.map_map, Function.comp_def]
  have hs (i : ℕ) (hi : i < k) : (of x).s.get? i = (of y).s.get? i := by
    rw [coeff x, coeff y, hd i hi]
  have conts_eq (n : ℕ) (hn : n ≤ k + 1) : (of x).contsAux n = (of y).contsAux n := by
    induction n using Nat.twoStepInduction with
    | zero => rfl
    | one => simp only [first_contAux_eq_h_one, h]
    | more n ih ih' =>
      simp only [contsAux, hs n (by omega), ih (by omega), ih' (by omega)]
  simp only [conv_eq_conts_a_div_conts_b, nth_cont_eq_succ_nth_contAux,
    conts_eq (k + 1) le_rfl]

private theorem two_pow_le_fib_mul (k : ℕ) : 2 ^ k ≤ Nat.fib (k + 1) * Nat.fib (k + 2) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hd : 2 * Nat.fib (k + 1) ≤ Nat.fib (k + 3) := by
      rw [Nat.fib_add_two (n := k + 1), two_mul]
      exact Nat.add_le_add_left Nat.fib_le_fib_succ _
    calc
      2 ^ (k + 1) ≤ (Nat.fib (k + 1) * Nat.fib (k + 2)) * 2 := by
        rw [pow_succ]
        exact Nat.mul_le_mul_right _ ih
      _ = Nat.fib (k + 2) * (2 * Nat.fib (k + 1)) := by ac_rfl
      _ ≤ Nat.fib (k + 2) * Nat.fib (k + 3) := Nat.mul_le_mul_left _ hd

private theorem abs_sub_conv_le (x : ℝ) (k : ℕ) : |x - (of x).convs k| ≤ 1 / 2 ^ k := by
  by_cases ht : (of x).TerminatedAt k
  · rw [sub_eq_zero.mpr (of_correctness_of_terminatedAt ht), abs_zero]
    positivity
  apply (abs_sub_convs_le ht).trans
  apply one_div_le_one_div_of_le (by positivity)
  calc
    (2 : ℝ) ^ k ≤ (Nat.fib (k + 1) : ℝ) * (Nat.fib (k + 2) : ℝ) := by
      exact_mod_cast two_pow_le_fib_mul k
    _ ≤ (of x).dens k * (of x).dens (k + 1) := by
      apply mul_le_mul _ _ (Nat.cast_nonneg _) zero_le_of_den
      · exact succ_nth_fib_le_of_nth_den (Or.inr (mt (terminated_stable (Nat.sub_le k 1)) ht))
      · exact succ_nth_fib_le_of_nth_den (Or.inr (by simpa using ht))

end abs_sub_le_of_contFrac_prefix_eq

open abs_sub_le_of_contFrac_prefix_eq

/-- **Real numbers with a common continued fraction prefix are close.** Let $\xi$ and $\xi'$ be
real numbers with continued fraction expansions $[a_0; a_1, a_2, \dots]$ and
$[a_0'; a_1', a_2', \dots]$, computed by $\xi_0 = \xi$, $a_i = \lfloor \xi_i \rfloor$ and
$\xi_{i+1} = 1/(\xi_i - a_i)$, stopping when $\xi_i = a_i$ (so an expansion is finite exactly when
the number is rational). Let $k \ge 0$ be an integer, and suppose that $a_0 = a_0'$ and that for
each $1 \le i \le k$ either both expansions have a digit of index $i$ and $a_i = a_i'$, or neither
has one. Then $|\xi - \xi'| \le 2^{1-k}$.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Lemma 5 (`integers-2025-A47-lem-5`), quoted from Cusick and Flahive, Lemma 1. -/
public theorem abs_sub_le_of_contFrac_prefix_eq (ξ ξ' : ℝ) (k : ℕ)
    (h0 : (GenContFract.of ξ).h = (GenContFract.of ξ').h)
    (hk : ∀ i < k, (GenContFract.of ξ).partDens.get? i = (GenContFract.of ξ').partDens.get? i) :
    |ξ - ξ'| ≤ 2 ^ (1 - (k : ℤ)) := by
  have hc := convs_eq_of_prefix h0 hk
  calc
    |ξ - ξ'| ≤ |ξ - (of ξ).convs k| + |(of ξ).convs k - ξ'| := abs_sub_le _ _ _
    _ ≤ 1 / (2 : ℝ) ^ k + 1 / 2 ^ k := by
      apply add_le_add (abs_sub_conv_le ξ k)
      rw [hc, abs_sub_comm]
      exact abs_sub_conv_le ξ' k
    _ = 2 ^ (1 - (k : ℤ)) := by
      rw [zpow_sub₀ (by norm_num), zpow_one, zpow_natCast, ← add_div]
      norm_num

end MetaMathlibExt

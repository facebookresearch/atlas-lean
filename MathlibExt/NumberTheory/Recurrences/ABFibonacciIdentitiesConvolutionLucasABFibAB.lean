/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentities
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# A convolution of (a, b)-Lucas and (a, d)-Fibonacci numbers

The convolution `∑ i ∈ Finset.Icc 1 n, L^{a,b}_{n-i} F^{a,d}_i`, scaled by `b - d`,
equals the difference `L^{a,b}_{n+1} - L^{a,d}_{n+1}` of the Lucas numbers, and the
convolution itself is symmetric in the second parameters `b` and `d`.

Statements from Emil Daniel Schwab, "Fibonacci
Numbers via Dirichlet Convolution and Lucas Numbers
via Unitary Convolution", *Journal of Integer
Sequences* 28 (2025), Article 25.1.7
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Schwab/schwab3.html>).
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentitiesWanted

/-- Lucas numbers through Fibonacci numbers: `L_m = 2 F_{m+1} - a F_m`, since both sides
share the initial values and the defining recurrence. -/
private theorem lucasAB_eq_two_mul_fibAB_succ_sub (a b : ℂ) (m : ℕ) :
    lucasAB a b m = 2 * fibAB a b (m + 1) - a * fibAB a b m := by
  induction m using Nat.twoStepInduction with
  | zero => simp [fibAB, lucasAB]
  | one => simp [fibAB, lucasAB]; ring
  | more k ih₀ ih₁ =>
    have e : k + 2 + 1 = (k + 1) + 2 := by omega
    rw [e]
    simp only [lucasAB_add_two, fibAB_add_two, ih₀, ih₁]
    ring

/-- One step of the convolution: peeling the last two terms and applying the Lucas
recurrence to the rest expresses `S(n+2)` through `S(n+1)` and `S(n)`. -/
private theorem conv_step (a b d : ℂ) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 (n + 2), lucasAB a b (n + 2 - i) * fibAB a d i =
      a * (∑ i ∈ Finset.Icc 1 (n + 1), lucasAB a b (n + 1 - i) * fibAB a d i) +
      b * (∑ i ∈ Finset.Icc 1 n, lucasAB a b (n - i) * fibAB a d i) +
      (-a * fibAB a d (n + 1) + 2 * fibAB a d (n + 2)) := by
  have e1a : (∑ i ∈ Finset.Icc 1 (n + 2), lucasAB a b (n + 2 - i) * fibAB a d i) =
      (∑ i ∈ Finset.Icc 1 (n + 1), lucasAB a b (n + 2 - i) * fibAB a d i) +
      lucasAB a b (n + 2 - (n + 2)) * fibAB a d (n + 2) := by
    have h := Finset.sum_Icc_succ_top (a := 1) (b := n + 1) (by omega)
      (fun i => lucasAB a b (n + 2 - i) * fibAB a d i)
    simpa only [(by omega : n + 1 + 1 = n + 2)] using h
  have e1b : (∑ i ∈ Finset.Icc 1 (n + 1), lucasAB a b (n + 2 - i) * fibAB a d i) =
      (∑ i ∈ Finset.Icc 1 n, lucasAB a b (n + 2 - i) * fibAB a d i) +
      lucasAB a b 1 * fibAB a d (n + 1) := by
    have h := Finset.sum_Icc_succ_top (a := 1) (b := n) (by omega)
      (fun i => lucasAB a b (n + 2 - i) * fibAB a d i)
    simpa only [(by omega : n + 2 - (n + 1) = 1)] using h
  have e2 : (∑ i ∈ Finset.Icc 1 n, lucasAB a b (n + 2 - i) * fibAB a d i) =
      a * (∑ i ∈ Finset.Icc 1 n, lucasAB a b (n + 1 - i) * fibAB a d i) +
      b * (∑ i ∈ Finset.Icc 1 n, lucasAB a b (n - i) * fibAB a d i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    have g1 : n + 2 - i = (n - i) + 2 := by omega
    have g2 : n + 1 - i = (n - i) + 1 := by omega
    rw [g1, g2, lucasAB_add_two]
    ring
  have e3 : (∑ i ∈ Finset.Icc 1 (n + 1), lucasAB a b (n + 1 - i) * fibAB a d i) =
      (∑ i ∈ Finset.Icc 1 n, lucasAB a b (n + 1 - i) * fibAB a d i) +
      lucasAB a b 0 * fibAB a d (n + 1) := by
    have h := Finset.sum_Icc_succ_top (a := 1) (b := n) (by omega)
      (fun i => lucasAB a b (n + 1 - i) * fibAB a d i)
    simpa only [(by omega : n + 1 - (n + 1) = 0)] using h
  rw [e1a, e1b, e2, e3]
  simp only [lucasAB_zero, lucasAB_one, Nat.sub_self]
  ring

/-- The scaled convolution identity, which holds for all `b` and `d` (at `b = d` both sides
are zero); the hypothesis `b ≠ d` is only needed for the symmetric form below. -/
private theorem scaled_conv (a b d : ℂ) (n : ℕ) :
    (b - d) * ∑ i ∈ Finset.Icc 1 n, lucasAB a b (n - i) * fibAB a d i =
      lucasAB a b (n + 1) - lucasAB a d (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [show Finset.Icc 1 (0 : ℕ) = ∅ from by decide, Finset.sum_empty, mul_zero]
    change (0 : ℂ) = lucasAB a b 1 - lucasAB a d 1
    rw [lucasAB_one, lucasAB_one, sub_self]
  | one =>
    rw [Finset.Icc_self, Finset.sum_singleton, Nat.sub_self, lucasAB_zero, fibAB_one,
      mul_one]
    have h2b : lucasAB a b (1 + 1) = a * lucasAB a b 1 + b * lucasAB a b 0 :=
      lucasAB_add_two a b 0
    have h2d : lucasAB a d (1 + 1) = a * lucasAB a d 1 + d * lucasAB a d 0 :=
      lucasAB_add_two a d 0
    rw [h2b, h2d, lucasAB_one, lucasAB_one, lucasAB_zero, lucasAB_zero]
    ring
  | more n ih₀ ih₁ =>
    have hS := conv_step a b d n
    have ih₁' : (b - d) * (∑ i ∈ Finset.Icc 1 (n + 1),
          lucasAB a b (n + 1 - i) * fibAB a d i) =
        lucasAB a b (n + 2) - lucasAB a d (n + 2) := by
      simpa only [(by omega : n + 1 + 1 = n + 2)] using ih₁
    have hLb : lucasAB a b (n + 2 + 1) =
        a * lucasAB a b (n + 2) + b * lucasAB a b (n + 1) := by
      have h := lucasAB_add_two a b (n + 1)
      simpa only [(by omega : n + 1 + 2 = n + 2 + 1),
        (by omega : n + 1 + 1 = n + 2)] using h
    have hLd : lucasAB a d (n + 2 + 1) =
        a * lucasAB a d (n + 2) + d * lucasAB a d (n + 1) := by
      have h := lucasAB_add_two a d (n + 1)
      simpa only [(by omega : n + 1 + 2 = n + 2 + 1),
        (by omega : n + 1 + 1 = n + 2)] using h
    have hL : lucasAB a d (n + 1) =
        2 * fibAB a d (n + 2) - a * fibAB a d (n + 1) :=
      lucasAB_eq_two_mul_fibAB_succ_sub a d (n + 1)
    linear_combination (b - d) * hS + a * ih₁' + b * ih₀ - hLb + hLd - (b - d) * hL

/-- **A convolution of (a, b)-Lucas and (a, d)-Fibonacci numbers.** Let $a, b, d$ be complex
numbers with $b \ne d$, and write $L^{a,b}_n$ for the $(a,b)$-Lucas numbers and $F^{a,b}_n$ for
the $(a,b)$-Fibonacci numbers. Then for every natural number $n$,
$$(b - d) \sum_{i=1}^{n} L^{a,b}_{n-i} F^{a,d}_i = L^{a,b}_{n+1} - L^{a,d}_{n+1}$$
and
$$\sum_{i=1}^{n} L^{a,b}_{n-i} F^{a,d}_i = \sum_{i=1}^{n} L^{a,d}_{n-i} F^{a,b}_i.$$

The source states the first identity in divided form,
$\sum_{i=1}^{n} L^{a,b}_{n-i} F^{a,d}_i = (L^{a,b}_{n+1} - L^{a,d}_{n+1})/(b - d)$.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Corollary 14(a). -/
theorem convolution_lucasAB_fibAB (a b d : ℂ) (hbd : b ≠ d)
    (n : ℕ) :
    (b - d) * ∑ i ∈ Finset.Icc 1 n,
          lucasAB a b (n - i) * fibAB a d i =
        lucasAB a b (n + 1) - lucasAB a d (n + 1) ∧
      ∑ i ∈ Finset.Icc 1 n, lucasAB a b (n - i) * fibAB a d i =
        ∑ i ∈ Finset.Icc 1 n, lucasAB a d (n - i) * fibAB a b i := by
  refine ⟨scaled_conv a b d n, ?_⟩
  have h1 := scaled_conv a b d n
  have h2 := scaled_conv a d b n
  have hcancel : (b - d) * (∑ i ∈ Finset.Icc 1 n,
      lucasAB a b (n - i) * fibAB a d i) =
      (b - d) * (∑ i ∈ Finset.Icc 1 n,
        lucasAB a d (n - i) * fibAB a b i) := by
    linear_combination h1 + h2
  exact mul_left_cancel₀ (sub_ne_zero.mpr hbd) hcancel

end MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentitiesWanted

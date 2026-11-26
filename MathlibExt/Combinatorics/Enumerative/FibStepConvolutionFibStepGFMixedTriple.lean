/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.Enumerative.FibStepConvolution
public import MathlibExt.NumberTheory.PellNumberSequence
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.GetD
import Mathlib.Tactic.LinearCombination

/-!
# Generating-function form of the triple convolution with two consecutive step sequences

This module proves `fibStepGF_mixed_triple`: for natural numbers `m ≥ 1` and `p ≥ 1`, the
generating functions `fibStepGF` of the Fibonacci step numbers satisfy `X^m F^{(m)} F^{(m+1)}
F^{(p)} = F^{(p)} F^{(m+1)} - F^{(p)} F^{(m)}` in `ℚ⟦X⟧`.

Source: Robert Frontczak and Karol Gryszka, "General Convolution Sums Involving Fibonacci
`m`-Step Numbers", *Journal of Integer Sequences* 27 (2024), Article 24.8.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Gryszka/gryszka12.tex>), Theorem 25.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted

private lemma length_fibStepSeq (m n : ℕ) : (fibStepSeq m n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n => simp [fibStepSeq, ih]

private lemma getD_fibStepSeq (m n k : ℕ) (hk : k ≤ n) :
    (fibStepSeq m n).getD k 0 = fibStep m k := by
  induction n with
  | zero =>
    obtain rfl : k = 0 := by omega
    rfl
  | succ n ih =>
    obtain h | rfl := lt_or_eq_of_le hk
    · cases n with
      | zero =>
        obtain rfl : k = 0 := by omega
        rfl
      | succ n =>
        rw [fibStepSeq, List.getD_append _ _ _ _ (by simpa [length_fibStepSeq] using h)]
        exact ih (by omega)
    · rfl

private lemma fibStep_add_two (m n : ℕ) :
    fibStep m (n + 2) = ∑ j ∈ Finset.Icc 1 m, fibStep m (n + 2 - j) := by
  rw [fibStep, fibStepSeq, List.getD_append_right _ _ _ _ (by simp [length_fibStepSeq])]
  simp only [length_fibStepSeq, Nat.sub_self, List.getD_cons_zero]
  exact Finset.sum_congr rfl fun j hj =>
    getD_fibStepSeq m (n + 1) _ (by have := (Finset.mem_Icc.mp hj).1; omega)

open PowerSeries

private lemma coeff_shift (m j n : ℕ) :
    coeff n (X ^ j * fibStepGF m) = (fibStep m (n - j) : ℚ) := by
  rw [coeff_X_pow_mul']
  split_ifs with hj
  · exact coeff_mk ..
  · rw [Nat.sub_eq_zero_of_le (by omega)]
    rfl

private lemma fibStepGF_denom (m : ℕ) :
    (1 - ∑ j ∈ Finset.Icc 1 m, X ^ j) * fibStepGF m = X := by
  ext n
  simp only [sub_mul, one_mul, Finset.sum_mul, map_sub, map_sum, coeff_shift, coeff_X]
  rw [fibStepGF, coeff_mk]
  have h0 : fibStep m 0 = 0 := rfl
  match n with
  | 0 => simp [h0]
  | 1 =>
    have hz (j : ℕ) (hj : j ∈ Finset.Icc 1 m) : (fibStep m (1 - j) : ℚ) = 0 := by
      simp [Nat.sub_eq_zero_of_le (Finset.mem_Icc.mp hj).1, h0]
    simp [Finset.sum_eq_zero hz, show fibStep m 1 = 1 from rfl]
  | n + 2 => simp [fibStep_add_two m n]

private lemma fibStepGF_sub_succ (m : ℕ) :
    fibStepGF m - fibStepGF (m + 1) =
      -(X ^ m) * fibStepGF m * fibStepGF (m + 1) := by
  have hm := fibStepGF_denom m
  have hs := fibStepGF_denom (m + 1)
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), pow_succ] at hs
  apply X_mul_cancel
  linear_combination fibStepGF (m + 1) * hm - fibStepGF m * hs

-- The lower bounds match the source statement; the step-difference identity needs no hypothesis.
set_option linter.unusedVariables false in
/-- **Generating-function form of the triple convolution with two consecutive step sequences.**
For a natural number $s$ let $F^{(s)}(X) = \sum_{n \ge 0} F^{(s)}_n X^n$ be the ordinary
generating function, with rational coefficients, of the Fibonacci $s$-step numbers
$F^{(s)}_n$. For all natural numbers $m \ge 1$ and $p \ge 1$, the formal power series over
$\mathbb{Q}$ satisfy
$$
X^m F^{(m)}(X) F^{(m+1)}(X) F^{(p)}(X) = F^{(p)}(X) F^{(m+1)}(X) - F^{(p)}(X) F^{(m)}(X).
$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 25. -/
theorem fibStepGF_mixed_triple (m p : ℕ) (hm : 1 ≤ m)
    (hp : 1 ≤ p) :
    PowerSeries.X ^ m * fibStepGF m * fibStepGF (m + 1) *
        fibStepGF p =
      fibStepGF p * fibStepGF (m + 1) - fibStepGF p * fibStepGF m := by
  have hsub := fibStepGF_sub_succ m
  linear_combination fibStepGF p * hsub

end MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted

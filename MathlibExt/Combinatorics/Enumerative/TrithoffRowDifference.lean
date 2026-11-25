/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.GetD
public import MathlibExt.NumberTheory.TribonacciSequenceWithInitialValues001

/-!
# Differences along a Trithoff row

Placing zeros at the least significant end shifts each Tribonacci weight. The difference
between the third and second shifts equals the Tribonacci value of the adjacent-digit sums.
-/

namespace MetaMathlibExt

/-- **Tribonacci representation.** Let $T_n$ be the Tribonacci numbers, $T_0 = T_1 = 0$,
$T_2 = 1$ and $T_{n+3} = T_{n+2} + T_{n+1} + T_n$. A list $w = (w_0, \dots, w_{\ell-1})$ of
natural numbers, read least significant digit first, is a Tribonacci representation of a
natural number $n$ when every digit $w_i$ is $0$ or $1$, no three consecutive entries of $w$
are all equal to $1$, and $n = \sum_{i=0}^{\ell-1} w_i T_{i+3}$. Leading zeros (trailing
entries of $w$) are allowed.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 2.3 (Tribonacci representation). -/
@[expose] public def IsTribonacciRepr (w : List ℕ) (n : ℕ) : Prop :=
  (∀ d ∈ w, d ≤ 1) ∧ ¬ [1, 1, 1] <:+: w ∧
    ∑ i ∈ Finset.range w.length, w.getD i 0 * tribonacci (i + 3) = n

/-- **Tribonacci value of a digit word.** Let $T_0 = T_1 = 0$, $T_2 = 1$ and
$T_{k+3} = T_{k+2} + T_{k+1} + T_k$ be the Tribonacci numbers. The Tribonacci value of a finite
word $w$ of natural-number digits $w_0, w_1, \dots, w_{\ell-1}$, listed from the least
significant digit, is $[w]_T = \sum_{i=0}^{\ell-1} w_i T_{i+3}$, so the digits weigh
$1, 2, 4, 7, 13, \dots$. Digits may exceed $1$ and three consecutive ones are allowed, so this
also evaluates the paper's non-canonical and improper representations.

For a Tribonacci representation $w$ of $n$, the value of $w$ followed by a new least
significant digit $0$ is the Tribonacci successor $\mathrm{out}(n)$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Sections 2.3, 5 and 6.1. -/
@[expose] public def tribonacciValue (w : List ℕ) : ℕ :=
  ∑ i ∈ Finset.range w.length, w.getD i 0 * tribonacci (i + 3)

namespace exists_trithoff_row_difference_eq

/-- The digit sum with every Tribonacci weight shifted up by `k` places. -/
private def shiftedValue (a : List ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range a.length, a.getD i 0 * tribonacci (i + 3 + k)

private theorem shiftedValue_zero_cons (a : List ℕ) (k : ℕ) :
    shiftedValue (0 :: a) k = shiftedValue a (k + 1) := by
  simp [shiftedValue, Finset.sum_range_succ', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem shiftedValue_three (a : List ℕ) :
    shiftedValue a 3 = shiftedValue a 2 + (shiftedValue a 0 + shiftedValue a 1) := by
  unfold shiftedValue
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [tribonacci]
  simp only [Nat.add_zero, Nat.mul_add]
  ac_rfl

/-- Adding adjacent digits adds the values of the original word and its one-place shift. -/
private theorem value_adjacent (a : List ℕ) :
    tribonacciValue ((List.range (a.length + 1)).map fun i => a.getD i 0 + (0 :: a).getD i 0) =
      shiftedValue a 0 + shiftedValue a 1 := by
  rw [← shiftedValue_zero_cons a 0]
  unfold tribonacciValue shiftedValue
  simp only [List.length_map, List.length_range, List.length_cons, Nat.add_zero]
  calc
    _ = ∑ i ∈ Finset.range (a.length + 1),
          (a.getD i 0 + (0 :: a).getD i 0) * tribonacci (i + 3) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [List.getD_eq_getElem _ _ (by simpa using hi')]
      simp
    _ = _ := by
      simp_rw [Nat.add_mul, Finset.sum_add_distrib]
      rw [Finset.sum_range_succ (fun i => a.getD i 0 * tribonacci (i + 3))]
      simp

end exists_trithoff_row_difference_eq

open exists_trithoff_row_difference_eq

set_option linter.unusedVariables false in
/-- **Differences along a Trithoff row.** Let $T_0 = T_1 = 0$, $T_2 = 1$ and
$T_{m+3} = T_{m+2} + T_{m+1} + T_m$ be the Tribonacci numbers, and for a finite word
$w = (w_0, \dots, w_{\ell-1})$ of natural-number digits, listed from the least significant
digit, let $[w]_T = \sum_{i=0}^{\ell-1} w_i T_{i+3}$ be its Tribonacci value. Let
$a = (a_0, \dots, a_{\ell-1})$ be a Tribonacci representation of a natural number $n$ (all
digits $0$ or $1$, no three consecutive ones, and $[a]_T = n$), and let
$b = (b_0, \dots, b_\ell)$ be the word with $b_i = a_i + a_{i-1}$, where $a_{-1} = a_\ell = 0$
(the product $11 \cdot a$ computed digit-wise without carries). For $k \ge 0$ write $0^k a$ for
the word $(0, \dots, 0, a_0, \dots, a_{\ell-1})$ with $k$ zeros placed before $a_0$, that is, at
the least significant end. Then there is a natural number $k$ with
$[0^{k+1} a]_T - [0^k a]_T = [b]_T$.

The entries of the Trithoff row of $n$ from $n$ onwards are $[0^k a]_T$ for $k \ge 0$, so
$[b]_T$ is the difference of two consecutive entries of that row.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Proposition 8 (`jis-2025-25.5.4-prop-8`). -/
public theorem exists_trithoff_row_difference_eq (a : List ℕ) (n : ℕ)
    (h : IsTribonacciRepr a n) :
    ∃ k : ℕ, (tribonacciValue (List.replicate (k + 1) 0 ++ a) : ℤ) -
        tribonacciValue (List.replicate k 0 ++ a) =
      tribonacciValue ((List.range (a.length + 1)).map fun i =>
        a.getD i 0 + (0 :: a).getD i 0) := by
  refine ⟨2, ?_⟩
  rw [value_adjacent]
  change (shiftedValue (0 :: 0 :: 0 :: a) 0 : ℤ) - shiftedValue (0 :: 0 :: a) 0 = _
  simp only [shiftedValue_zero_cons, Nat.reduceAdd]
  rw [shiftedValue_three]
  omega

end MetaMathlibExt

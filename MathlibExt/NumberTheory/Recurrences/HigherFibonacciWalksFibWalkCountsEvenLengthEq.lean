/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalks
import Mathlib.Tactic.Linarith

/-!
# Halving the Fibonacci self-convolution at even length

`fibWalkCounts_even_length_eq` expresses the even and odd parts of the Fibonacci
self-convolution at even length in terms of the full sum and a Fibonacci number.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles and Self-Convolutions of
Higher-Order Fibonacci Numbers", *Journal of Integer Sequences* 29 (2026), Article 26.3.7,
Theorem 6.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted

private lemma fibQ_add_two (n : ℤ) : fibQ (n + 2) = fibQ n + fibQ (n + 1) := by
  exact_mod_cast Int.fib_add_two n

private lemma filtered_sum_recurrence (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    (∑ j ∈ (Finset.range (n + 2 + 1)).filter p,
      fibQ ((j : ℤ) + 1) * fibQ (((n + 2 : ℕ) : ℤ) - j + 1)) =
      (∑ j ∈ (Finset.range (n + 1 + 1)).filter p,
        fibQ ((j : ℤ) + 1) * fibQ (((n + 1 : ℕ) : ℤ) - j + 1)) +
      (∑ j ∈ (Finset.range (n + 1)).filter p,
        fibQ ((j : ℤ) + 1) * fibQ ((n : ℤ) - j + 1)) +
      if p (n + 2) then fibQ ((n : ℤ) + 3) else 0 := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_range_succ]
  rw [← Finset.sum_filter]
  have hrec (j : ℕ) :
      fibQ (((n + 2 : ℕ) : ℤ) - j + 1) =
        fibQ (((n + 1 : ℕ) : ℤ) - j + 1) + fibQ ((n : ℤ) - j + 1) := by
    have hindex : ((n + 2 : ℕ) : ℤ) - j + 1 = ((n : ℤ) - j + 1) + 2 := by omega
    have hindex' : ((n + 1 : ℕ) : ℤ) - j + 1 = ((n : ℤ) - j + 1) + 1 := by omega
    rw [hindex, hindex', fibQ_add_two, add_comm]
  conv_lhs =>
    arg 1
    arg 2
    ext j
    rw [hrec j, mul_add]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_filter]
  rw [Finset.sum_range_succ (f := fun j =>
    if p j then fibQ ((j : ℤ) + 1) * fibQ ((n : ℤ) - j + 1) else 0)]
  simp [fibQ, Nat.cast_add, add_assoc]

private lemma even_odd_sum (n : ℕ) :
    evenFibWalkCount n + oddFibWalkCount n = fibWalkCount n := by
  simpa only [evenFibWalkCount, oddFibWalkCount, fibWalkCount, Nat.not_even_iff_odd] using
    Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1)) Even
      (fun j => fibQ ((j : ℤ) + 1) * fibQ ((n : ℤ) - j + 1))

private lemma even_odd_difference (k : ℕ) :
    evenFibWalkCount (2 * k) - oddFibWalkCount (2 * k) = fibQ (2 * (k : ℤ) + 2) := by
  induction k with
  | zero => simp [evenFibWalkCount, oddFibWalkCount, Finset.sum_filter, fibQ]
  | succ k ih =>
    have he := filtered_sum_recurrence Even (2 * k)
    have ho := filtered_sum_recurrence Odd (2 * k)
    have hodd := evenFibWalkCount_odd_length_eq_oddFibWalkCount (k + 1) (by omega)
    have hindex : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    rw [hindex] at hodd
    have hrec := fibQ_add_two (2 * (k : ℤ) + 2)
    have hp : Even (2 * k + 2) := by simp [Nat.even_iff]
    have hp' : ¬ Odd (2 * k + 2) := by simp [Nat.odd_iff]
    change evenFibWalkCount (2 * k + 2) =
      evenFibWalkCount (2 * k + 1) + evenFibWalkCount (2 * k) +
        (if Even (2 * k + 2) then fibQ (((2 * k : ℕ) : ℤ) + 3) else 0) at he
    change oddFibWalkCount (2 * k + 2) =
      oddFibWalkCount (2 * k + 1) + oddFibWalkCount (2 * k) +
        (if Odd (2 * k + 2) then fibQ (((2 * k : ℕ) : ℤ) + 3) else 0) at ho
    simp only [hp, ite_true] at he
    simp only [hp', ite_false, add_zero] at ho
    have hn : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [hn]
    norm_num [Nat.cast_succ, mul_add, add_assoc] at he hrec ⊢
    linarith

/-- **Halving the Fibonacci self-convolution at even length.** Let $F_n$ denote the Fibonacci
numbers ($F_0 = 0$, $F_1 = 1$) and, for $n \ge 0$, let $v_n = \sum_{j=0}^{n} F_{j+1} F_{n-j+1}$,
and let $E_n$ and $O_n$ be the sums of the same terms $F_{j+1} F_{n-j+1}$ over the even and over
the odd integers $j$ with $0 \le j \le n$. For every integer $k \ge 1$,
$E_{2k} = (v_{2k} + F_{2k+2})/2$ and $O_{2k} = (v_{2k} - F_{2k+2})/2$.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Theorem 6. -/
theorem fibWalkCounts_even_length_eq
    (k : ℕ) (hk : 1 ≤ k) :
    evenFibWalkCount (2 * k) =
        (fibWalkCount (2 * k) + fibQ (2 * (k : ℤ) + 2)) / 2 ∧
      oddFibWalkCount (2 * k) =
        (fibWalkCount (2 * k) - fibQ (2 * (k : ℤ) + 2)) / 2
    := by
  have hsum := even_odd_sum (2 * k)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hdiff := even_odd_difference (1 + j)
  constructor <;> linarith

end MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted

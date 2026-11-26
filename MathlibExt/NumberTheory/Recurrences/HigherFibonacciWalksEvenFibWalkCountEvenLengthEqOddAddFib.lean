/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalks
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Even and odd parts of the Fibonacci self-convolution at even length

The alternating difference `altFibWalkDiff` equals `evenFibWalkCount - oddFibWalkCount`
and satisfies a two-step recurrence; `alt_two_mul_and_succ` evaluates it at even and odd
indices. `evenFibWalkCount_even_length_eq_odd_add_fib` proves that at even length the even
part exceeds the odd part by a Fibonacci number.

Statements from Jan Sedlák and Antonín Slavík, "Walks in Tiled
Rectangles and Self-Convolutions of Higher-Order Fibonacci Numbers",
*Journal of Integer Sequences* 29 (2026), Article 26.3.7
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Slavik/slavik4.html>).
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted

private def altFibWalkDiff (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n + 1),
    (-1 : ℚ) ^ j * (fibQ ((j : ℤ) + 1) * fibQ ((n : ℤ) - (j : ℤ) + 1))

private theorem fibQ_add_two (n : ℤ) : fibQ (n + 2) = fibQ n + fibQ (n + 1) := by
  simp only [fibQ, Int.fib_add_two]
  push_cast
  ring

private theorem fibQ_zero : fibQ 0 = 0 := by simp [fibQ]

private theorem fibQ_one : fibQ 1 = 1 := by simp [fibQ]

private theorem alt_eq_sub (n : ℕ) :
    altFibWalkDiff n = evenFibWalkCount n - oddFibWalkCount n := by
  unfold altFibWalkDiff evenFibWalkCount oddFibWalkCount
  have h := Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1)) Even
    (fun j => (-1 : ℚ) ^ j * (fibQ ((j : ℤ) + 1) * fibQ ((n : ℤ) - (j : ℤ) + 1)))
  have he : ∑ j ∈ (Finset.range (n + 1)).filter Even,
      (-1 : ℚ) ^ j * (fibQ ((j : ℤ) + 1) * fibQ ((n : ℤ) - (j : ℤ) + 1))
      = ∑ j ∈ (Finset.range (n + 1)).filter Even,
      fibQ ((j : ℤ) + 1) * fibQ ((n : ℤ) - (j : ℤ) + 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    have heven : Even j := (Finset.mem_filter.mp hj).2
    rw [heven.neg_one_pow]
    ring
  have ho : ∑ j ∈ (Finset.range (n + 1)).filter (fun j => ¬ Even j),
      (-1 : ℚ) ^ j * (fibQ ((j : ℤ) + 1) * fibQ ((n : ℤ) - (j : ℤ) + 1))
      = - ∑ j ∈ (Finset.range (n + 1)).filter Odd,
      fibQ ((j : ℤ) + 1) * fibQ ((n : ℤ) - (j : ℤ) + 1) := by
    have hfilter : (Finset.range (n + 1)).filter (fun j => ¬ Even j)
        = (Finset.range (n + 1)).filter Odd := by
      apply Finset.filter_congr
      intro j _
      exact Nat.not_even_iff_odd
    rw [hfilter, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hodd : Odd j := (Finset.mem_filter.mp hj).2
    rw [hodd.neg_one_pow]
    ring
  rw [he, ho] at h
  rw [← h]
  ring

private theorem fibQ_split (m j : ℕ) :
    fibQ ((m : ℤ) - (j : ℤ) + 1)
      = fibQ ((m : ℤ) - (j : ℤ)) + fibQ ((m : ℤ) - (j : ℤ) - 1) := by
  have h : (m : ℤ) - (j : ℤ) + 1 = ((m : ℤ) - (j : ℤ) - 1) + 2 := by ring
  have h2 : ((m : ℤ) - (j : ℤ) - 1) + 1 = (m : ℤ) - (j : ℤ) := by ring
  rw [h, fibQ_add_two, h2]
  ring

private theorem alt_recurrence (m : ℕ) (hm : 2 ≤ m) :
    altFibWalkDiff m
      = altFibWalkDiff (m - 1) + altFibWalkDiff (m - 2)
        + (-1 : ℚ) ^ m * fibQ ((m : ℤ) + 1) := by
  have h1 : m - 1 + 1 = m := by omega
  have h2 : m - 2 + 1 = m - 1 := by omega
  have hcast1 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
  have hcast2 : ((m - 2 : ℕ) : ℤ) = (m : ℤ) - 2 := by omega
  unfold altFibWalkDiff
  rw [h1, h2]
  rw [Finset.sum_range_succ]
  have hlast : (-1 : ℚ) ^ m * (fibQ ((m : ℤ) + 1) * fibQ ((m : ℤ) - (m : ℤ) + 1))
      = (-1 : ℚ) ^ m * fibQ ((m : ℤ) + 1) := by
    have hidx : (m : ℤ) - (m : ℤ) + 1 = 1 := by ring
    rw [hidx, fibQ_one]
    ring
  rw [hlast]
  have hsplit : ∀ j ∈ Finset.range m,
      (-1 : ℚ) ^ j * (fibQ ((j : ℤ) + 1) * fibQ ((m : ℤ) - (j : ℤ) + 1))
      = (-1 : ℚ) ^ j * (fibQ ((j : ℤ) + 1) * fibQ ((m : ℤ) - (j : ℤ)))
        + (-1 : ℚ) ^ j * (fibQ ((j : ℤ) + 1) * fibQ ((m : ℤ) - (j : ℤ) - 1)) := by
    intro j _
    rw [fibQ_split]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl
      intro j _
      have hidx : ((m - 1 : ℕ) : ℤ) - (j : ℤ) + 1 = (m : ℤ) - (j : ℤ) := by
        rw [hcast1]
        ring
      rw [hidx]
    · have hm_eq : m = (m - 1) + 1 := by omega
      conv_lhs => rw [hm_eq, Finset.sum_range_succ]
      have hzero : (-1 : ℚ) ^ (m - 1)
          * (fibQ (((m - 1 : ℕ) : ℤ) + 1)
            * fibQ (((m - 1 + 1 : ℕ) : ℤ) - ((m - 1 : ℕ) : ℤ) - 1)) = 0 := by
        have hidx0 : ((m - 1 + 1 : ℕ) : ℤ) - ((m - 1 : ℕ) : ℤ) - 1 = 0 := by
          rw [h1, hcast1]
          ring
        rw [hidx0, fibQ_zero]
        ring
      rw [hzero, add_zero]
      apply Finset.sum_congr rfl
      intro j _
      have hcastm : ((m - 1 + 1 : ℕ) : ℤ) = (m : ℤ) := by rw [h1]
      have hidx : ((m - 2 : ℕ) : ℤ) - (j : ℤ) + 1
          = ((m - 1 + 1 : ℕ) : ℤ) - (j : ℤ) - 1 := by
        rw [hcastm, hcast2]
        ring
      rw [hidx]

private theorem alt_zero : altFibWalkDiff 0 = fibQ 2 := by
  simp [altFibWalkDiff, fibQ]

private theorem alt_one : altFibWalkDiff 1 = 0 := by
  simp [altFibWalkDiff, fibQ, Finset.sum_range_succ]

private theorem alt_two_mul_and_succ (k : ℕ) :
    altFibWalkDiff (2 * k) = fibQ (2 * (k : ℤ) + 2)
      ∧ altFibWalkDiff (2 * k + 1) = 0 := by
  induction k with
  | zero =>
    have h0 : (2 * 0 : ℕ) = 0 := by ring
    have h1 : (2 * 0 + 1 : ℕ) = 1 := by ring
    have hc : (2 * ((0 : ℕ) : ℤ) + 2) = 2 := by simp
    rw [h0, h1, hc]
    exact ⟨alt_zero, alt_one⟩
  | succ k ih =>
    obtain ⟨ih_even, ih_odd⟩ := ih
    have e1 : 2 * (k + 1) = 2 * k + 2 := by ring
    have e2 : 2 * (k + 1) + 1 = 2 * k + 3 := by ring
    have hm1_ge : 2 ≤ 2 * k + 2 := by omega
    have hm1_sub1 : (2 * k + 2) - 1 = 2 * k + 1 := by omega
    have hm1_sub2 : (2 * k + 2) - 2 = 2 * k := by omega
    have heven1 : Even (2 * k + 2) := ⟨k + 1, by ring⟩
    have hpow1 : (-1 : ℚ) ^ (2 * k + 2) = 1 := heven1.neg_one_pow
    have hcast_m1 : ((2 * k + 2 : ℕ) : ℤ) = 2 * (k : ℤ) + 2 := by push_cast; ring
    have hrec1 := alt_recurrence (2 * k + 2) hm1_ge
    rw [hm1_sub1, hm1_sub2, hpow1, hcast_m1] at hrec1
    have hfib1 : fibQ (2 * (k : ℤ) + 4) = fibQ (2 * (k : ℤ) + 2) + fibQ (2 * (k : ℤ) + 3) := by
      have h := fibQ_add_two (2 * (k : ℤ) + 2)
      have ha : (2 * (k : ℤ) + 2) + 2 = 2 * (k : ℤ) + 4 := by ring
      have hb : (2 * (k : ℤ) + 2) + 1 = 2 * (k : ℤ) + 3 := by ring
      rw [ha, hb] at h
      exact h
    have heven_new : altFibWalkDiff (2 * k + 2) = fibQ (2 * (k : ℤ) + 4) := by
      rw [hrec1, ih_odd, ih_even]
      have hid : (2 * (k : ℤ) + 2) + 1 = 2 * (k : ℤ) + 3 := by ring
      rw [hid]
      calc 0 + fibQ (2 * ↑k + 2) + 1 * fibQ (2 * ↑k + 3)
          = fibQ (2 * ↑k + 2) + fibQ (2 * ↑k + 3) := by ring
        _ = fibQ (2 * ↑k + 4) := hfib1.symm
    have hm2_ge : 2 ≤ 2 * k + 3 := by omega
    have hm2_sub1 : (2 * k + 3) - 1 = 2 * k + 2 := by omega
    have hm2_sub2 : (2 * k + 3) - 2 = 2 * k + 1 := by omega
    have hodd2 : Odd (2 * k + 3) := ⟨k + 1, by ring⟩
    have hpow2 : (-1 : ℚ) ^ (2 * k + 3) = -1 := hodd2.neg_one_pow
    have hcast_m2 : ((2 * k + 3 : ℕ) : ℤ) = 2 * (k : ℤ) + 3 := by push_cast; ring
    have hrec2 := alt_recurrence (2 * k + 3) hm2_ge
    rw [hm2_sub1, hm2_sub2, hpow2, hcast_m2] at hrec2
    have hodd_new : altFibWalkDiff (2 * k + 3) = 0 := by
      rw [hrec2, heven_new, ih_odd]
      have hid : (2 * (k : ℤ) + 3) + 1 = 2 * (k : ℤ) + 4 := by ring
      rw [hid]
      ring
    have hgoal_cast : 2 * (((k + 1 : ℕ)) : ℤ) + 2 = 2 * (k : ℤ) + 4 := by push_cast; ring
    rw [e2, e1, hgoal_cast]
    exact ⟨heven_new, hodd_new⟩

/-- **Even and odd parts of the Fibonacci self-convolution at even length.** Let $F_n$ denote
the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$) and, for $n \ge 0$, let $E_n$ and $O_n$ be the
sums of $F_{j+1} F_{n-j+1}$ over the even and over the odd integers $j$ with $0 \le j \le n$.
For every integer $k \ge 1$, $E_{2k} = O_{2k} + F_{2k+2}$.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Lemma 5. -/
theorem evenFibWalkCount_even_length_eq_odd_add_fib
    (k : ℕ) (hk : 1 ≤ k) :
    evenFibWalkCount (2 * k) =
      oddFibWalkCount (2 * k) + fibQ (2 * (k : ℤ) + 2) := by
  have _ : 1 ≤ k := hk
  have h1 : altFibWalkDiff (2 * k)
      = evenFibWalkCount (2 * k) - oddFibWalkCount (2 * k) :=
    alt_eq_sub _
  have h2 : altFibWalkDiff (2 * k) = fibQ (2 * (k : ℤ) + 2) :=
    (alt_two_mul_and_succ k).1
  have h : evenFibWalkCount (2 * k) - oddFibWalkCount (2 * k)
      = fibQ (2 * (k : ℤ) + 2) := by
    rw [← h1, h2]
  linear_combination h

end MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted

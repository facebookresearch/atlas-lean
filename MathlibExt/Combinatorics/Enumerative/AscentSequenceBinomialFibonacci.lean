/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# A binomial sum for odd Fibonacci numbers

The binomial terms count placements of marked tiles alternating in lengths one
and two, with two choices for each unmarked tile (of length one). Pascal's
identity gives a recurrence for each choice of starting length. Starting with
a length-two marked tile gives the odd Fibonacci subsequence; starting with
a length-one marked tile gives the even subsequence.

The identity is the first sum of Proposition 2(i) evaluated in Proposition 3
of [Callan and Mansour, INTEGERS 25 (2025), A80](https://math.colgate.edu/~integers/z80/z80.pdf),
with the two empty-sum cases included.
-/

namespace MetaMathlibExt

open Finset

/-- Weight of `r` marked tiles with `d` extra units of length, at total length `m`. -/
private def tileWeight (m r d : ℕ) : ℕ :=
  if r + d ≤ m then (m - d).choose r * 2 ^ (m - d - r) else 0

private theorem tileWeight_zero (m : ℕ) : tileWeight m 0 0 = 2 ^ m := by
  simp [tileWeight]

private theorem tileWeight_eq_zero {m r d : ℕ} (h : m < r + d) :
    tileWeight m r d = 0 := by
  simp [tileWeight, Nat.not_le.mpr h]

private theorem tileWeight_shift (m r d : ℕ) :
    tileWeight (m + 1) r (d + 1) = tileWeight m r d := by
  have h : r + (d + 1) ≤ m + 1 ↔ r + d ≤ m := by omega
  simp [tileWeight, h, show m + 1 - (d + 1) = m - d by omega]

private theorem tileWeight_pascal (m r d : ℕ) :
    tileWeight (m + 1) (r + 1) d =
      2 * tileWeight m (r + 1) d + tileWeight m r d := by
  by_cases h : r + d ≤ m
  · have h' : r + 1 + d ≤ m + 1 := by omega
    have htop : m + 1 - d = (m - d) + 1 := by omega
    have hexp : m - d + 1 - (r + 1) = m - d - r := by omega
    simp only [tileWeight, ite_eq_left h, ite_eq_left h', htop, Nat.choose_succ_succ, hexp]
    by_cases hr : r + 1 + d ≤ m
    · rw [ite_eq_left hr, show m - d - r = m - d - (r + 1) + 1 by omega, pow_succ]
      ring
    · have heq : m - d = r := by omega
      simp [hr, heq]
  · rw [tileWeight_eq_zero (by omega), tileWeight_eq_zero (by omega),
      tileWeight_eq_zero (by omega)]

/-- Sum over the feasible numbers of marked tiles; `d` specifies their extra length. -/
private def tileSum (d : ℕ → ℕ) (m : ℕ) : ℕ :=
  ∑ r ∈ range (m + 1), tileWeight m r (d r)

private theorem tileSum_step (d : ℕ → ℕ) (hd : d 0 = 0) (m : ℕ) :
    tileSum d (m + 1) = 2 * tileSum d m + tileSum (fun r ↦ d (r + 1)) m := by
  have hzero : tileWeight m (m + 1) (d (m + 1)) = 0 := tileWeight_eq_zero (by omega)
  have htail : (∑ r ∈ range (m + 1), tileWeight m (r + 1) (d (r + 1))) + 2 ^ m =
      tileSum d m := by
    unfold tileSum
    rw [Finset.sum_range_succ _ m, hzero, add_zero, Finset.sum_range_succ' _ m,
      hd, tileWeight_zero]
  calc
    tileSum d (m + 1) =
        2 * ((∑ r ∈ range (m + 1), tileWeight m (r + 1) (d (r + 1))) + 2 ^ m) +
          tileSum (fun r ↦ d (r + 1)) m := by
      unfold tileSum
      rw [Finset.sum_range_succ' _ (m + 1)]
      simp only [hd, tileWeight_zero, tileWeight_pascal, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [pow_succ]
      ring
    _ = _ := by rw [htail]

private abbrev shortFirst := tileSum (fun r ↦ r / 2)
private abbrev longFirst := tileSum (fun r ↦ (r + 1) / 2)

private theorem shortFirst_step (m : ℕ) :
    shortFirst (m + 1) = 2 * shortFirst m + longFirst m :=
  tileSum_step _ rfl m

private theorem longFirst_step (m : ℕ) :
    longFirst (m + 2) = 2 * longFirst (m + 1) + shortFirst m := by
  change tileSum (fun r ↦ (r + 1) / 2) (m + 1 + 1) = _
  rw [tileSum_step _ rfl (m + 1)]
  congr 1
  unfold shortFirst tileSum
  have hzero : tileWeight (m + 1) (m + 1) ((m + 1 + 1 + 1) / 2) = 0 :=
    tileWeight_eq_zero (by omega)
  rw [Finset.sum_range_succ _ (m + 1), hzero, add_zero]
  apply Finset.sum_congr rfl
  intro r _
  change tileWeight (m + 1) r ((r + 1 + 1) / 2) = _
  rw [show (r + 1 + 1) / 2 = r / 2 + 1 by omega, tileWeight_shift]

private theorem fib_step_two (j : ℕ) :
    Nat.fib (j + 3) = 2 * Nat.fib (j + 1) + Nat.fib j := by
  rw [show j + 3 = (j + 1) + 2 by omega, Nat.fib_add_two,
    show j + 1 + 1 = j + 2 by omega, Nat.fib_add_two]
  omega

/-- The two tile sums satisfy coupled recurrences, as do the odd and even Fibonacci numbers. -/
private theorem tileSum_eq_fib (m : ℕ) :
    longFirst m = Nat.fib (2 * m + 1) ∧
      longFirst (m + 1) = Nat.fib (2 * m + 3) ∧
      shortFirst m = Nat.fib (2 * m + 2) := by
  induction m with
  | zero => decide
  | succ m ih =>
    obtain ⟨h₀, h₁, h₂⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · simpa [Nat.mul_succ, Nat.add_assoc] using h₁
    · rw [longFirst_step, h₁, h₂, show 2 * (m + 1) + 3 = (2 * m + 2) + 3 by omega,
        fib_step_two (2 * m + 2), show 2 * m + 2 + 1 = 2 * m + 3 by omega]
    · rw [shortFirst_step, h₂, h₀, show 2 * (m + 1) + 2 = (2 * m + 1) + 3 by omega,
        fib_step_two (2 * m + 1), show 2 * m + 1 + 1 = 2 * m + 2 by omega]

/-- Group the positive indices into the pairs `(2*k-1, 2*k)`. -/
private theorem sum_range_pairs (f : ℕ → ℕ) (K : ℕ) :
    (∑ r ∈ range (2 * K + 1), f r) =
      (∑ k ∈ range K, (f (2 * (k + 1)) + f (2 * (k + 1) - 1))) + f 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show 2 * (K + 1) + 1 = ((2 * K + 1) + 1) + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ,
      show 2 * K + 1 + 1 = 2 * (K + 1) by omega,
      show 2 * (K + 1) - 1 = 2 * K + 1 by omega]
    ac_rfl

/-- Reindex the tile sum by writing the positive number of marks as `2*k` or `2*k-1`. -/
private theorem longFirst_eq_sum (n : ℕ) (hn : 4 ≤ n) :
    longFirst (n - 4) =
      (∑ k ∈ Icc 1 (n / 3 - 1),
        (Nat.choose (n - k - 4) (2 * k) * 2 ^ (n - 3 * k - 4) +
          Nat.choose (n - k - 4) (2 * k - 1) * 2 ^ (n - 3 * k - 3))) + 2 ^ (n - 4) := by
  have support : ∀ r, 2 * (n / 3 - 1) < r → n - 4 < r + (r + 1) / 2 := by
    intro r hr
    omega
  unfold longFirst tileSum
  rw [← Finset.sum_subset (s₁ := range (2 * (n / 3 - 1) + 1))
    (Finset.range_mono (by omega)) (fun r _ hr ↦ tileWeight_eq_zero (support r (by
      simp only [Finset.mem_range] at hr
      omega))), sum_range_pairs]
  simp only [show (0 + 1) / 2 = (0 : ℕ) by decide, tileWeight_zero]
  congr 1
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  rw [show 1 + i = i + 1 by omega]
  generalize hk : i + 1 = k
  have heven : (2 * k + 1) / 2 = k := by omega
  have hodd : (2 * k - 1 + 1) / 2 = k := by omega
  have htop : n - 4 - k = n - k - 4 := by omega
  have he : n - k - 4 - 2 * k = n - 3 * k - 4 := by omega
  have ho : n - k - 4 - (2 * k - 1) = n - 3 * k - 3 := by omega
  have hodd_le : 2 * k - 1 + k ≤ n - 4 := by omega
  simp only [heven, hodd, tileWeight, ite_eq_left hodd_le, htop, he, ho]
  -- At the upper endpoint when `3 ∣ n`, only the odd index is feasible.
  split_ifs with h
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by omega : n - k - 4 < 2 * k), zero_mul]

/-- **Fibonacci closed form of a binomial sum with powers of two.** Let $F_m$ denote the
Fibonacci numbers, with $F_0 = 0$ and $F_1 = 1$. For every natural number $n \ge 4$,
$$\sum_{k=1}^{\lfloor n/3 \rfloor - 1} \left( \binom{n-k-4}{2k} 2^{n-3k-4} +
\binom{n-k-4}{2k-1} 2^{n-3k-3} \right) + 2^{n-4} = F_{2n-7}.$$
The sum is empty for $n < 6$. When $3$ divides $n$, the last index $k = n/3 - 1$ gives the
exponent $n - 3k - 4 = -1$, but there $\binom{n-k-4}{2k} = 0$, and the product
$\binom{n-k-4}{2k} 2^{n-3k-4}$ is read as $0$; the other product in that summand is $1$.

The source states this as the sum being $F_{2n-7} - 2^{n-4}$. The summand is reconstructed from
an extracted display of the source's Proposition 2(i), as the full text was not available; exact
computation confirms the identity for $4 \le n \le 500$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Proposition 3 (`integers-2025-A80-prop-3`), with the sum of Proposition 2(i). -/
public theorem sum_choose_mul_two_pow_add_two_pow_eq_fib (n : ℕ) (hn : 4 ≤ n) :
    (∑ k ∈ Finset.Icc 1 (n / 3 - 1),
        (Nat.choose (n - k - 4) (2 * k) * 2 ^ (n - 3 * k - 4) +
          Nat.choose (n - k - 4) (2 * k - 1) * 2 ^ (n - 3 * k - 3))) + 2 ^ (n - 4) =
      Nat.fib (2 * n - 7) := by
  rw [← longFirst_eq_sum n hn, (tileSum_eq_fib (n - 4)).1]
  congr 1
  omega

end MetaMathlibExt

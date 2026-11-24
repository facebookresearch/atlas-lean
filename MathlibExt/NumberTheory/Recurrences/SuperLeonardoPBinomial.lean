/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.NumberTheory.Recurrences.SuperLeonardoP
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Explicit formula for the supergeneralized Leonardo p-numbers

`fibonacciP_succ_eq_sum_choose` writes the Fibonacci p-numbers as sums of binomial coefficients.
The binomial sums in `superLeonardoP_eq_sum_choose` give the coefficients of the initial
values and of the constant increment in the Leonardo recurrence.
-/

namespace MetaMathlibExt

-- Offset zero gives the weights of the initial values. Offset one gives the weight of k.
private def diagonalSum (p t r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (t / (p + 1) + 1), (t - i * p).choose (i + r)

private theorem diagonalSum_initial (p t r : ℕ) (ht : t ≤ p) :
    diagonalSum p t r = t.choose r := by
  simp [diagonalSum, Nat.div_eq_of_lt (show t < p + 1 by omega)]

private theorem diagonalSum_extend (p t r b : ℕ) (hb : t / (p + 1) < b) :
    diagonalSum p t r = ∑ i ∈ Finset.range b, (t - i * p).choose (i + r) := by
  apply Finset.sum_subset (Finset.range_mono hb)
  intro i _ hi
  simp only [Finset.mem_range, not_lt] at hi
  have h := (Nat.div_lt_iff_lt_mul (by omega : 0 < p + 1)).mp hi
  rw [Nat.mul_add, Nat.mul_one] at h
  have hi_pos : 0 < i := (Nat.zero_le _).trans_lt hi
  exact Nat.choose_eq_zero_of_lt (by omega)

-- Away from the first summand, Pascal's identity relates two successive diagonals.
private theorem diagonalSum_step (p t r : ℕ) :
    diagonalSum p (t + p + 1) r + (t + p).choose r =
      diagonalSum p (t + p) r + diagonalSum p t r + (t + p + 1).choose r := by
  let b := t + p + 1
  have bound {u v : ℕ} (h : u < v) : u / (p + 1) < v := (Nat.div_le_self ..).trans_lt h
  rw [diagonalSum_extend p (t + p + 1) r (b + 1) (bound (by dsimp [b]; omega)),
    diagonalSum_extend p (t + p) r (b + 1) (bound (by dsimp [b]; omega)),
    diagonalSum_extend p t r b (bound (by dsimp [b]; omega))]
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun i => (t + p - i * p).choose (i + r))]
  simp only [Nat.zero_mul, Nat.sub_zero, Nat.zero_add]
  have hsplit (i : ℕ) :
      (t + p + 1 - (i + 1) * p).choose (i + 1 + r) =
        (t + p - (i + 1) * p).choose (i + 1 + r) + (t - i * p).choose (i + r) := by
    rw [Nat.add_mul, Nat.one_mul]
    by_cases hi : i * p ≤ t
    · rw [show t + p + 1 - (i * p + p) = (t - i * p) + 1 by omega,
        show t + p - (i * p + p) = t - i * p by omega,
        show i + 1 + r = (i + r) + 1 by omega, Nat.choose_succ_succ', Nat.add_comm]
    · have hi_pos : 0 < i := Nat.pos_of_ne_zero (fun h => hi (by simp [h]))
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega),
        Nat.choose_eq_zero_of_lt (by omega), Nat.zero_add]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  ac_rfl

/-- **Binomial sum formula for Fibonacci p-numbers.** For all natural numbers $p \ge 1$ and $n$,
the Fibonacci $p$-numbers $F_p$ satisfy
$$F_p(n+1) = \sum_{i=0}^{\lfloor n/(p+1) \rfloor} \binom{n-ip}{i}.$$

The paper (Theorem 8, quoting Kuhapatanakul) also gives the form
$F_p(n) = \sum_{i=0}^{\lfloor (n-1)/(p+1) \rfloor} \binom{n-1-ip}{i}$, which is the same identity
with $n$ shifted by one. The paper allows all natural $p$, but at $p = 0$ the sequence is
identically zero ($F_0(1) = F_0(0) + F_0(0) = 0$) while the sum at $n = 0$ is
$\binom{0}{0} = 1$, so $p \ge 1$ is assumed.

Source: Clemens Schütz and Kristian Kelly, *An Explicit Formula for Supergeneralized
Leonardo `p`-numbers*, Journal of Integer Sequences 28 (2025), Article 25.8.2,
Theorem 8 (Kuhapatanakul). -/
public theorem fibonacciP_succ_eq_sum_choose (p n : ℕ) (hp : 1 ≤ p) :
    fibonacciP p (n + 1) = ∑ i ∈ Finset.range (n / (p + 1) + 1), (n - i * p).choose i := by
  -- The right side is the diagonal sum with offset zero.
  change fibonacciP p (n + 1) = diagonalSum p n 0
  induction n using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t ≤ p
    · rw [diagonalSum_initial p t 0 ht, Nat.choose_zero_right]
      by_cases h : t + 1 ≤ p
      · exact fibonacciP_eq_one p (t + 1) (by omega) h
      · obtain rfl : t = p := by omega
        rw [fibonacciP_rec t (t + 1) (by omega)]
        simp [fibonacciP_eq_one t t hp le_rfl]
    · obtain ⟨b, rfl⟩ : ∃ b, t = b + p + 1 := ⟨t - p - 1, by omega⟩
      rw [fibonacciP_rec p (b + p + 1 + 1) (by omega)]
      simp only [Nat.add_sub_cancel, show b + p + 1 + 1 - p - 1 = b + 1 by omega,
        ih (b + p) (by omega), ih b (by omega)]
      simpa using (diagonalSum_step p b 0).symm

private theorem diagonalSum_one_succ (p t : ℕ) :
    diagonalSum p (t + 1) 1 = diagonalSum p t 1 + diagonalSum p (t - p) 1 + 1 := by
  by_cases ht : t < p
  · simp [diagonalSum_initial p (t + 1) 1 (by omega), diagonalSum_initial p t 1 ht.le,
      Nat.sub_eq_zero_of_le ht.le, diagonalSum_initial p 0 1 (Nat.zero_le p)]
  · have h := diagonalSum_step p (t - p) 1
    rw [show t - p + p = t by omega] at h
    simp only [Nat.choose_one_right] at h
    omega

private theorem superLeonardoP_forcing (p k : ℕ) (x : ℕ → ℝ) (n : ℕ) :
    superLeonardoP p k x n =
      superLeonardoP p 0 x n + (diagonalSum p (n - p) 1 : ℝ) * k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n ≤ p
    · simp [superLeonardoP_of_le p k x hn, superLeonardoP_of_le p 0 x hn,
        Nat.sub_eq_zero_of_le hn, diagonalSum_initial p 0 1 (Nat.zero_le p)]
    · obtain ⟨b, rfl⟩ : ∃ b, n = b + p + 1 := ⟨n - p - 1, by omega⟩
      rw [superLeonardoP_of_lt p k x (by omega : p < b + p + 1),
        superLeonardoP_of_lt p 0 x (by omega : p < b + p + 1)]
      simp only [Nat.add_sub_cancel, show b + p + 1 - p = b + 1 by omega,
        ih (b + p) (by omega), ih b (by omega), diagonalSum_one_succ p b, Nat.cast_add,
        Nat.cast_one, Nat.cast_zero]
      ring

/-- **Explicit formula for the supergeneralized Leonardo p-numbers.** For all natural numbers
$p \ge 1$, $k$ and $n$ with $n > p$ and every real sequence $x$, the supergeneralized Leonardo
$p$-numbers $\mathcal{L}_{p,k,x}$ satisfy
$$\mathcal{L}_{p,k,x}(n) =
\Big(\sum_{i=0}^{\lfloor (n-p)/(p+1) \rfloor} \binom{n-p-ip}{i}\Big) x_p +
\sum_{i=0}^{\min(p-1,\,n-p-1)} \Big(\sum_{j=0}^{\lfloor (n-p-i-1)/(p+1) \rfloor}
\binom{n-p-i-1-jp}{j}\Big) x_i +
\max\Big\{0, \sum_{j=0}^{\lfloor (n-p)/(p+1) \rfloor} \binom{n-p-pj}{j+1}\Big\} \cdot k.$$

This is Theorem 9 of the paper with the factor $k$ restored: as in Corollary 7, the printed
theorem omits the factor $k$ on the last term and is false without it (same counterexample:
$p = 1$, $k = 2$, $n = 2$, $x = (1, 1)$ gives $4$ versus $3$).

Source: Clemens Schütz and Kristian Kelly, *An Explicit Formula for Supergeneralized
Leonardo `p`-numbers*, Journal of Integer Sequences 28 (2025), Article 25.8.2,
Theorem 9. -/
public theorem superLeonardoP_eq_sum_choose (p k : ℕ) (hp : 1 ≤ p) (x : ℕ → ℝ) (n : ℕ)
    (hn : p < n) :
    superLeonardoP p k x n =
      (∑ i ∈ Finset.range ((n - p) / (p + 1) + 1), ((n - p - i * p).choose i : ℝ)) * x p +
        (∑ i ∈ Finset.range (min (p - 1) (n - p - 1) + 1),
          (∑ j ∈ Finset.range ((n - p - i - 1) / (p + 1) + 1),
            ((n - p - i - 1 - j * p).choose j : ℝ)) * x i) +
        max 0 (∑ j ∈ Finset.range ((n - p) / (p + 1) + 1),
          ((n - p - p * j).choose (j + 1) : ℝ)) * k := by
  rw [superLeonardoP_forcing, superLeonardoP_zero_eq p hp, ite_eq_right (by omega)]
  have weight (t : ℕ) : (fibonacciP p (t + 1) : ℝ) =
      ∑ j ∈ Finset.range (t / (p + 1) + 1), ((t - j * p).choose j : ℝ) := by
    rw [fibonacciP_succ_eq_sum_choose p t hp, Nat.cast_sum]
  rw [weight]
  congr 2
  · apply Finset.sum_congr rfl
    intro i hi
    have := Finset.mem_range.mp hi
    have h : 1 ≤ n - p - i := by omega
    congr 1
    simpa only [Nat.sub_add_cancel h] using weight (n - p - i - 1)
  · rw [← Nat.cast_sum, max_eq_right (Nat.cast_nonneg _)]
    simp only [diagonalSum, Nat.mul_comm p]

end MetaMathlibExt

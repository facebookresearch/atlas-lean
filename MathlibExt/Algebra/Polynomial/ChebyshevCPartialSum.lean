/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Partial sums of the monic Chebyshev polynomials

The generating function of the partial sums has numerator `1 + t` and denominator
`1 - X * t + t ^ 2`. The Chebyshev recurrence gives the cancellation in degrees two and above.
For the binomial expansion, `F_n = S_n + S_{n-1}` with `S_n = Chebyshev.S ℤ n`, and Pascal's
rule gives the coefficients of `S_n`.
-/

open Polynomial

namespace MetaMathlibExt

/-- **Partial sums of the monic Chebyshev polynomials.** For $n \ge 0$, $F_n(X)$ is the
polynomial with integer coefficients
$$F_n(X) = 1 + \sum_{k=1}^{n} \bar T_k(X),$$
where $\bar T_k \in \mathbb{Z}[X]$ is the monic Chebyshev polynomial of the source, that is, the
polynomial with $\bar T_k(q + q^{-1}) = q^k + q^{-k}$; equivalently $\bar T_0 = 2$,
$\bar T_1 = X$ and $\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$. Thus $F_0 = 1$ and
$F_n = F_{n-1} + \bar T_n$ for $n \ge 1$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, (3.6)–(3.7). -/
@[expose] public noncomputable def chebyshevCPartialSum (n : ℕ) : ℤ[X] :=
  1 + ∑ k ∈ Finset.Icc 1 n, Chebyshev.C ℤ k

/-- **Zeroth partial sum of the Chebyshev polynomials.** Let
$F_n = 1 + \sum_{k=1}^{n} \bar T_k \in \mathbb{Z}[X]$ be the partial sums of the monic Chebyshev
polynomials $\bar T_k$ ($\bar T_0 = 2$, $\bar T_1 = X$, $\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$).
Then $F_0 = 1$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, (3.6). -/
public theorem chebyshevCPartialSum_zero : chebyshevCPartialSum 0 = 1 := by
  simp [chebyshevCPartialSum]

/-- **Successive partial sums of the Chebyshev polynomials.** Let
$F_n = 1 + \sum_{k=1}^{n} \bar T_k \in \mathbb{Z}[X]$ be the partial sums of the monic Chebyshev
polynomials $\bar T_k$ ($\bar T_0 = 2$, $\bar T_1 = X$, $\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$).
For every natural number $n$, $F_{n+1} = F_n + \bar T_{n+1}$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, (3.6). -/
public theorem chebyshevCPartialSum_succ (n : ℕ) :
    chebyshevCPartialSum (n + 1) = chebyshevCPartialSum n + Chebyshev.C ℤ (n + 1 : ℕ) := by
  simp only [chebyshevCPartialSum, Finset.sum_Icc_succ_top (Nat.le_add_left 1 n), add_assoc]

/-- **First and second partial sums of the Chebyshev polynomials.** Let
$F_n = 1 + \sum_{k=1}^{n} \bar T_k \in \mathbb{Z}[X]$ be the partial sums of the monic Chebyshev
polynomials $\bar T_k$ ($\bar T_0 = 2$, $\bar T_1 = X$, $\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$).
Then $F_1 = X + 1$ and $F_2 = X^2 + X - 1$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Table 4. -/
public theorem chebyshevCPartialSum_one_two :
    chebyshevCPartialSum 1 = X + 1 ∧ chebyshevCPartialSum 2 = X ^ 2 + X - 1 := by
  have h1 : chebyshevCPartialSum 1 = X + 1 := by
    rw [chebyshevCPartialSum_succ, chebyshevCPartialSum_zero]
    simp [add_comm]
  refine ⟨h1, ?_⟩
  rw [chebyshevCPartialSum_succ, h1]
  have hc : Chebyshev.C ℤ ((1 + 1 : ℕ) : ℤ) = X ^ 2 - 2 := by
    simpa using Chebyshev.C_two (R := ℤ)
  rw [hc]
  ring

/-- **Generating function of the partial sums of Chebyshev polynomials.** Let
$F_n = 1 + \sum_{k=1}^{n} \bar T_k \in \mathbb{Z}[X]$ be the partial sums of the monic Chebyshev
polynomials $\bar T_k$ ($\bar T_0 = 2$, $\bar T_1 = X$, $\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$).
In the ring $\mathbb{Z}[X][[t]]$ of formal power series in $t$ over $\mathbb{Z}[X]$,
$$(1 - X t + t^2) \sum_{n \ge 0} F_n t^n = 1 + t.$$

Since $1 - X t + t^2$ is a unit in $\mathbb{Z}[X][[t]]$, this is equivalent to
$\sum_{n \ge 0} F_n t^n = (1 + t)/(1 - X t + t^2)$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 3.3
(`jis-2026-26.4.4-prop-8`). -/
public theorem chebyshevCPartialSum_generatingFunction :
    (1 - PowerSeries.C X * PowerSeries.X + PowerSeries.X ^ 2) *
        PowerSeries.mk (fun n => chebyshevCPartialSum n) =
      (1 + PowerSeries.X : PowerSeries ℤ[X]) := by
  rw [add_mul, sub_mul, one_mul, pow_two, mul_assoc, mul_assoc]
  apply PowerSeries.ext
  intro n
  match n with
  | 0 => simp [chebyshevCPartialSum_zero]
  | 1 => simp [chebyshevCPartialSum_zero, chebyshevCPartialSum_one_two.1, PowerSeries.coeff_one]
  | n + 2 =>
    suffices chebyshevCPartialSum (n + 2) - X * chebyshevCPartialSum (n + 1) +
        chebyshevCPartialSum n = 0 by simpa [PowerSeries.coeff_one, PowerSeries.coeff_X]
    induction n with
    | zero =>
      rw [chebyshevCPartialSum_one_two.2, chebyshevCPartialSum_one_two.1,
        chebyshevCPartialSum_zero]
      ring
    | succ n ih =>
      -- The difference between consecutive coefficients vanishes by the Chebyshev recurrence.
      linear_combination (norm := (push_cast; ring_nf))
        ih + chebyshevCPartialSum_succ (n + 2) -
        X * chebyshevCPartialSum_succ (n + 1) + chebyshevCPartialSum_succ n +
        Chebyshev.C_add_two ℤ (n + 1)

/-- **Three-term recurrence for the partial sums of Chebyshev polynomials.** Let
$F_n = 1 + \sum_{k=1}^{n} \bar T_k \in \mathbb{Z}[X]$ be the partial sums of the monic Chebyshev
polynomials $\bar T_k$ ($\bar T_0 = 2$, $\bar T_1 = X$, $\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$).
For every $k \ge 1$, $F_{k+1} = X F_k - F_{k-1}$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 3.6
(`jis-2026-26.4.4-prop-11`). -/
public theorem chebyshevCPartialSum_recurrence (k : ℕ) (hk : 1 ≤ k) :
    chebyshevCPartialSum (k + 1) = X * chebyshevCPartialSum k - chebyshevCPartialSum (k - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have hcoeff := congrArg (PowerSeries.coeff (R := ℤ[X]) (n + 2))
    chebyshevCPartialSum_generatingFunction
  simp [add_mul, sub_mul, pow_two, mul_assoc, PowerSeries.coeff_one, PowerSeries.coeff_X] at hcoeff
  rw [Nat.succ_sub_one]
  linear_combination hcoeff

/- The binomial sum `∑_{m ≤ n/2} (-1)^m C(n-m, m) X^(n-2m)`, which is `Chebyshev.S ℤ n`. -/
private noncomputable def binomialSum (n : ℕ) : ℤ[X] :=
  ∑ m ∈ Finset.range (n / 2 + 1), (-1 : ℤ[X]) ^ m * ((n - m).choose m : ℤ[X]) * X ^ (n - 2 * m)

/- The terms with `n < 2 * m` vanish, so the binomial sum may run over any longer range. -/
private theorem binomialSum_eq_sum_range (n N : ℕ) (hN : n / 2 + 1 ≤ N) :
    binomialSum n =
      ∑ m ∈ Finset.range N, (-1 : ℤ[X]) ^ m * ((n - m).choose m : ℤ[X]) * X ^ (n - 2 * m) := by
  refine Finset.sum_subset (Finset.range_subset_range.2 hN) fun m _ hm => ?_
  rw [Finset.mem_range, not_lt] at hm
  rw [Nat.choose_eq_zero_of_lt (show n - m < m by omega), Nat.cast_zero, mul_zero, zero_mul]

/- Pascal's rule, term by term: the `(b + 1)`-st term of the binomial sum for `n + 2`. -/
private theorem binomialSum_term_add_two (n b : ℕ) :
    (-1 : ℤ[X]) ^ (b + 1) * ((n + 2 - (b + 1)).choose (b + 1) : ℤ[X]) *
        X ^ (n + 2 - 2 * (b + 1)) =
      X * ((-1 : ℤ[X]) ^ (b + 1) * ((n + 1 - (b + 1)).choose (b + 1) : ℤ[X]) *
          X ^ (n + 1 - 2 * (b + 1))) -
        (-1 : ℤ[X]) ^ b * ((n - b).choose b : ℤ[X]) * X ^ (n - 2 * b) := by
  have hpascal :
      (n + 2 - (b + 1)).choose (b + 1) = (n - b).choose b + (n - b).choose (b + 1) := by
    rcases le_or_gt b n with h | h
    · rw [show n + 2 - (b + 1) = n - b + 1 by omega, Nat.choose_succ_succ']
    · rw [Nat.choose_eq_zero_of_lt (show n + 2 - (b + 1) < b + 1 by omega),
        Nat.choose_eq_zero_of_lt (show n - b < b by omega),
        Nat.choose_eq_zero_of_lt (show n - b < b + 1 by omega)]
  -- When `n ≤ 2 * b` the binomial coefficient vanishes, otherwise the exponents agree.
  have hX : ((n - b).choose (b + 1) : ℤ[X]) * X ^ (n - 2 * b) =
      ((n - b).choose (b + 1) : ℤ[X]) * (X * X ^ (n + 1 - 2 * (b + 1))) := by
    rcases lt_or_ge (2 * b) n with h | h
    · rw [← pow_succ', show n + 1 - 2 * (b + 1) + 1 = n - 2 * b by omega]
    · rw [Nat.choose_eq_zero_of_lt (show n - b < b + 1 by omega), Nat.cast_zero, zero_mul,
        zero_mul]
  rw [hpascal, Nat.cast_add, show n + 2 - 2 * (b + 1) = n - 2 * b by omega,
    show n + 1 - (b + 1) = n - b by omega]
  linear_combination (-1 : ℤ[X]) ^ (b + 1) * hX

/- The binomial sums satisfy the recurrence of `Chebyshev.S`. -/
private theorem binomialSum_add_two (n : ℕ) :
    binomialSum (n + 2) = X * binomialSum (n + 1) - binomialSum n := by
  rw [binomialSum_eq_sum_range (n + 2) (n + 1 + 1) (by omega),
    binomialSum_eq_sum_range (n + 1) (n + 1 + 1) (by omega),
    binomialSum_eq_sum_range n (n + 1) (by omega), Finset.sum_range_succ' _ (n + 1),
    Finset.sum_range_succ' _ (n + 1), Finset.sum_congr rfl fun b _ => binomialSum_term_add_two n b,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [pow_zero, Nat.sub_zero, mul_zero, Nat.choose_zero_right, Nat.cast_one, one_mul]
  ring

/- `Chebyshev.S ℤ n` is the binomial sum, as both satisfy the same recurrence. -/
private theorem chebyshev_S_eq_binomialSum : ∀ n : ℕ, Chebyshev.S ℤ n = binomialSum n
  | 0 => by simp [binomialSum]
  | 1 => by simp [binomialSum]
  | n + 2 => by
    rw [binomialSum_add_two, ← chebyshev_S_eq_binomialSum n,
      ← chebyshev_S_eq_binomialSum (n + 1)]
    push_cast
    exact Chebyshev.S_add_two ℤ n

/- `F_n = S_n + S_{n-1}`, since `T̄_{n+1} = S_{n+1} - S_{n-1}`. -/
private theorem chebyshevCPartialSum_eq_S_add_S (n : ℕ) :
    chebyshevCPartialSum n = Chebyshev.S ℤ n + Chebyshev.S ℤ ((n : ℤ) - 1) := by
  induction n with
  | zero => simp [chebyshevCPartialSum_zero]
  | succ n ih =>
    rw [chebyshevCPartialSum_succ, ih, show ((n + 1 : ℕ) : ℤ) - 1 = n by push_cast; ring]
    push_cast
    linear_combination Chebyshev.S_sub_one ℤ (n : ℤ) - Chebyshev.S_eq_X_mul_S_add_C ℤ (n : ℤ)

/-- **Binomial expansion of the partial sums of Chebyshev polynomials.** Let
$F_n = 1 + \sum_{k=1}^{n} \bar T_k \in \mathbb{Z}[X]$ be the partial sums of the monic Chebyshev
polynomials $\bar T_k$ ($\bar T_0 = 2$, $\bar T_1 = X$, $\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$).
For every $n \ge 1$,
$$F_n = \sum_{m=0}^{\lfloor n/2 \rfloor} (-1)^m \binom{n-m}{m} X^{n-2m} +
\sum_{m=0}^{\lfloor (n-1)/2 \rfloor} (-1)^m \binom{n-m-1}{m} X^{n-2m-1}.$$

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 9
(`jis-2026-26.4.4-prop-9`). -/
public theorem chebyshevCPartialSum_eq_binomial_sum (n : ℕ) (hn : 1 ≤ n) :
    chebyshevCPartialSum n =
      ∑ m ∈ Finset.range (n / 2 + 1),
          (-1 : ℤ[X]) ^ m * ((n - m).choose m : ℤ[X]) * X ^ (n - 2 * m) +
        ∑ m ∈ Finset.range ((n - 1) / 2 + 1),
          (-1 : ℤ[X]) ^ m * ((n - m - 1).choose m : ℤ[X]) * X ^ (n - 2 * m - 1) := by
  rw [chebyshevCPartialSum_eq_S_add_S, show (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) by omega,
    chebyshev_S_eq_binomialSum, chebyshev_S_eq_binomialSum, binomialSum, binomialSum]
  -- The second sum is the binomial sum for `n - 1`, as `n - m - 1 = n - 1 - m`.
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Nat.sub_right_comm n m 1, Nat.sub_right_comm n (2 * m) 1]

end MetaMathlibExt

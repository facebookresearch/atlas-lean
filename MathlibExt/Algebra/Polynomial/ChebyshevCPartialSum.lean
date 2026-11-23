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

end MetaMathlibExt

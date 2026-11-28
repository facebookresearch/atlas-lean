/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Group.ForwardDiff
import MathlibExt.Data.Nat.Choose.AlternatingRowSums

/-! # Recurrence and generating function for the floor-exponent binomial sums -/

namespace MetaMathlibExt

open Finset

/-- **Recurrence for the floor-exponent binomial sums.** Let $R$ be a commutative ring, $t \in R$
and $\ell \ge 1$ an integer, and for $m \ge 0$ let
$T_\ell(m; t) = \sum_{j=0}^{m} \binom{m}{j} t^{\lfloor j/\ell \rfloor}$. Then for every integer
$n \ge 0$,
$$\sum_{i=0}^{\ell} (-1)^i \binom{\ell}{i} T_\ell(n+\ell-i; t) - t\, T_\ell(n; t) = 0.$$

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Theorem 4.2 (`fq-2024-florez11012023-thm-4.2`). -/
public theorem floorPowBinomialSum_recurrence {R : Type*} [CommRing R] (t : R) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (n : ℕ) :
    ∑ i ∈ range (ℓ + 1), (ℓ.choose i : R) * (-1) ^ i *
        ∑ j ∈ range (n + ℓ - i + 1), ((n + ℓ - i).choose j : R) * t ^ (j / ℓ) -
      t * ∑ j ∈ range (n + 1), (n.choose j : R) * t ^ (j / ℓ) = 0 := by
  -- A forward difference shifts the weight in the binomial sum by one place.
  let B (k m : ℕ) := ∑ j ∈ range (m + 1), (m.choose j : R) * t ^ ((j + k) / ℓ)
  have step (k : ℕ) : fwdDiff 1 (B k) = B (k + 1) := by
    funext m
    apply sub_eq_iff_eq_add'.mpr
    simpa only [B, Nat.succ_add, Nat.add_succ] using
      sum_choose_succ_mul (fun j _ ↦ t ^ ((j + k) / ℓ)) m
  have iter (k : ℕ) : (fwdDiff (1 : ℕ))^[k] (B 0) = B k := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, step]
  apply sub_eq_zero.mpr
  calc
    _ = (fwdDiff (1 : ℕ))^[ℓ] (B 0) n := by
      rw [fwdDiff_iter_eq_sum_shift, ← sum_range_reflect]
      refine sum_congr rfl fun i hi ↦ ?_
      have hiℓ : i ≤ ℓ := Nat.le_of_lt_succ (mem_range.mp hi)
      have hindex : n + ℓ - (ℓ - i) = n + i := by omega
      simp [B, hindex, Nat.choose_symm hiℓ, zsmul_eq_mul, mul_comm (ℓ.choose i : R)]
    _ = _ := by
      rw [iter, mul_sum]
      refine sum_congr rfl fun j _ ↦ ?_
      rw [Nat.add_div_right j hℓ, pow_succ]
      ac_rfl

/-- **Generating function of the floor-exponent binomial sums.** Let $R$ be a commutative ring,
$t \in R$ and $\ell \ge 1$ an integer, and for $n \ge 0$ let
$T_\ell(n; t) = \sum_{i=0}^{n} \binom{n}{i} t^{\lfloor i/\ell \rfloor}$. Then in the ring $R[[x]]$
of formal power series,
$$\Big(\sum_{n \ge 0} T_\ell(n; t)\, x^n\Big) \big((1-x)^\ell - t x^\ell\big)
  = \sum_{k=0}^{\ell-1} \Big(\sum_{i=0}^{k} (-1)^i \binom{i+\ell-k-1}{i}\Big) x^k.$$

So the generating function of the $T_\ell(n; t)$ is this polynomial divided by the series
$(1-x)^\ell - t x^\ell$, which is invertible since its constant term is $1$.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Theorem 4.4 (`fq-2024-florez11012023-thm-4.4`). -/
public theorem floorPowBinomialSum_generatingFunction {R : Type*} [CommRing R] (t : R)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    PowerSeries.mk (fun n => ∑ i ∈ range (n + 1), (n.choose i : R) * t ^ (i / ℓ)) *
        ((1 - PowerSeries.X) ^ ℓ - PowerSeries.C t * PowerSeries.X ^ ℓ) =
      ∑ k ∈ range ℓ, PowerSeries.C (∑ i ∈ range (k + 1),
        (-1 : R) ^ i * ((i + ℓ - k - 1).choose i : R)) * PowerSeries.X ^ k := by
  let T (n : ℕ) : R := ∑ i ∈ range (n + 1), (n.choose i : R) * t ^ (i / ℓ)
  let F := PowerSeries.mk T
  let a (i : ℕ) : R := (ℓ.choose i : R) * (-1) ^ i
  let b (k : ℕ) : R := ∑ i ∈ range (k + 1), (-1 : R) ^ i * ((i + ℓ - k - 1).choose i : R)
  have hpow : (1 - PowerSeries.X : PowerSeries R) ^ ℓ =
      ∑ i ∈ range (ℓ + 1), PowerSeries.C (a i) * PowerSeries.X ^ i := by
    rw [sub_eq_add_neg, add_comm, show -(PowerSeries.X : PowerSeries R) =
      PowerSeries.C (-1 : R) * PowerSeries.X by simp, add_pow]
    apply sum_congr rfl
    intro i _
    simp only [mul_pow, one_pow, mul_one, a, map_mul, map_pow, map_neg, map_one, map_natCast]
    ac_rfl
  have hcoeff (n i : ℕ) (c : R) :
      PowerSeries.coeff n (F * (PowerSeries.C c * PowerSeries.X ^ i)) =
        if i ≤ n then c * T (n - i) else 0 := by
    rw [← mul_assoc, PowerSeries.coeff_mul_X_pow']
    simp [F, mul_comm]
  -- Below degree ℓ, the weights are all one and the coefficients are alternating row sums.
  have hinitial (n : ℕ) (hn : n < ℓ) :
      ∑ i ∈ range (n + 1), a i * T (n - i) = b n := by
    have hT (i : ℕ) : T (n - i) = ∑ j ∈ range (n - i + 1), ((n - i).choose j : R) := by
      apply sum_congr rfl
      intro j hj
      have hj' : j < ℓ := by have := mem_range.mp hj; omega
      rw [Nat.div_eq_of_lt hj', pow_zero, mul_one]
    simp_rw [hT]
    have h := alternating_choose_mul_sum_choose ℓ n
    have hcast : (∑ i ∈ range (n + 1), (ℓ.choose i : R) * (-1) ^ i *
        ∑ j ∈ range (n - i + 1), ((n - i).choose j : R)) =
        ∑ i ∈ range (n + 1), (-1 : R) ^ i *
          (↑(Ring.choose ((i : ℤ) + ℓ - n - 1) i : ℤ) : R) := by
      simpa only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
        Int.cast_natCast] using congrArg (fun z : ℤ => (z : R)) h
    refine hcast.trans (sum_congr rfl fun i _ => ?_)
    have he : (i : ℤ) + ℓ - n - 1 = ((i + ℓ - n - 1 : ℕ) : ℤ) := by omega
    rw [he, Ring.choose_natCast, Int.cast_natCast]
  change F * ((1 - PowerSeries.X) ^ ℓ - PowerSeries.C t * PowerSeries.X ^ ℓ) =
    ∑ k ∈ range ℓ, PowerSeries.C (b k) * PowerSeries.X ^ k
  ext n
  rw [hpow, mul_sub, mul_sum, map_sub, map_sum, map_sum, hcoeff]
  simp_rw [hcoeff, PowerSeries.coeff_C_mul_X_pow]
  by_cases hn : n < ℓ
  · rw [ite_eq_right (by omega : ¬ ℓ ≤ n), sub_zero]
    have hrhs : (∑ k ∈ range ℓ, if n = k then b k else 0) = b n := by
      rw [sum_eq_single n]
      · simp
      · intro k _ hk
        exact ite_eq_right (Ne.symm hk)
      · exact fun h => (h (mem_range.mpr hn)).elim
    rw [hrhs, ← hinitial n hn]
    calc
      _ = ∑ i ∈ range (n + 1), if i ≤ n then a i * T (n - i) else 0 := by
        symm
        apply sum_subset (range_mono (by omega))
        intro i _ hi
        exact ite_eq_right (by simpa [mem_range, Nat.lt_succ_iff] using hi)
      _ = _ := sum_congr rfl fun i hi => ite_eq_left (Nat.le_of_lt_succ (mem_range.mp hi))
  · -- At degree ℓ or higher, the already-proved recurrence makes the coefficient zero.
    have hn' : ℓ ≤ n := Nat.le_of_not_gt hn
    rw [ite_eq_left hn']
    have hrhs : (∑ k ∈ range ℓ, if n = k then b k else 0) = 0 := by
      apply sum_eq_zero
      intro k hk
      exact ite_eq_right (by have := mem_range.mp hk; omega)
    rw [hrhs]
    have hrec := floorPowBinomialSum_recurrence t hℓ (n - ℓ)
    rw [Nat.sub_add_cancel hn'] at hrec
    change (∑ i ∈ range (ℓ + 1), a i * T (n - i)) - t * T (n - ℓ) = 0 at hrec
    rw [← hrec]
    congr 1
    apply sum_congr rfl
    intro i hi
    exact ite_eq_left (by have := mem_range.mp hi; omega)

end MetaMathlibExt

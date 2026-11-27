/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.Recurrences.GFPFibSumChoose

/-! # The Webb–Parberry binomial identity

The coefficient of `X^m` in the Fibonacci-type polynomial with recurrence `F(n+2) = F(n+1) +
X * F(n)` has two expressions. The usual Fibonacci polynomial gives a single binomial
coefficient; the odd part of a quadratic-algebra power gives the sum of binomial products.
-/

open Finset Polynomial
open scoped QuadraticAlgebra

namespace MetaMathlibExt

private theorem webb_parberry_binomial_part (n : ℕ) :
    ((ω + (1 : QuadraticAlgebra ℤ[X] (4 * X + 1) 0)) ^ n).im =
      ∑ j ∈ range ((n - 1) / 2 + 1), (n.choose (2 * j + 1) : ℤ[X]) * (4 * X + 1) ^ j := by
  let D : ℤ[X] := 4 * X + 1
  let ι := algebraMap ℤ[X] (QuadraticAlgebra ℤ[X] D 0)
  have even_pow (j : ℕ) : (ω : QuadraticAlgebra ℤ[X] D 0) ^ (2 * j) = ι (D ^ j) := by
    rw [pow_mul, map_pow]
    congr 1
    simp [sq, QuadraticAlgebra.omega_mul_omega_eq_algebraMap, ι]
  by_cases hn : n = 0
  · subst n
    simp
  rw [add_pow, ← QuadraticAlgebra.imₗ_apply, map_sum]
  symm
  refine sum_of_injOn (fun j ↦ 2 * j + 1) ?_ ?_ ?_ ?_
  · intro a _ b _ h
    change 2 * a + 1 = 2 * b + 1 at h
    omega
  · intro j hj
    simp only [SetLike.mem_coe, mem_range] at hj ⊢
    omega
  · intro l hl h
    obtain ⟨j, rfl | rfl⟩ := l.even_or_odd'
    · rw [even_pow j]
      have hi : (ι (D ^ j)).im = 0 := rfl
      simp only [one_pow, mul_one, QuadraticAlgebra.imₗ_apply, QuadraticAlgebra.im_mul,
        QuadraticAlgebra.im_natCast, hi, zero_mul, mul_zero, add_zero]
    · exact (h ⟨j, mem_range.mpr (by have := mem_range.mp hl; omega), rfl⟩).elim
  · intro j _
    have him : ((ω : QuadraticAlgebra ℤ[X] D 0) ^ (2 * j + 1)).im = D ^ j := by
      rw [pow_succ, even_pow]
      have hre : (ι (D ^ j)).re = D ^ j := rfl
      have him : (ι (D ^ j)).im = 0 := rfl
      simp only [QuadraticAlgebra.im_mul, hre, him, QuadraticAlgebra.re_omega,
        QuadraticAlgebra.im_omega, mul_one, mul_zero, add_zero]
    simp only [one_pow, mul_one, QuadraticAlgebra.imₗ_apply, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast, mul_zero, add_zero, him]
    ring

private theorem webb_parberry_scaled (n : ℕ) :
    (2 : ℤ[X]) ^ n * generalizedFibonacciPolynomial 0 1 1 X (n + 1) =
      ((ω + (1 : QuadraticAlgebra ℤ[X] (4 * X + 1) 0)) ^ (n + 1)).im := by
  let D : ℤ[X] := 4 * X + 1
  let z : QuadraticAlgebra ℤ[X] D 0 := ω + 1
  let ι := algebraMap ℤ[X] (QuadraticAlgebra ℤ[X] D 0)
  let F := generalizedFibonacciPolynomial 0 1 1 X
  have hz : z.re = 1 := by simp [z]
  have hz' : z.im = 1 := by simp [z]
  have hz2 : z ^ 2 = ι (2 : ℤ[X]) * z + ι (4 * X) := by
    apply QuadraticAlgebra.ext
    · simp [pow_two, ι, hz, hz', D]
      ring
    · norm_num [pow_two, ι, hz, hz']
  have himul (a : ℤ[X]) (w : QuadraticAlgebra ℤ[X] D 0) : (ι a * w).im = a * w.im := by
    have hre : (ι a).re = a := rfl
    have him : (ι a).im = 0 := rfl
    simp [hre, him]
  change (2 : ℤ[X]) ^ n * F (n + 1) = (z ^ (n + 1)).im
  induction n using Nat.twoStepInduction with
  | zero => simp [F, hz']
  | one =>
    rw [show 1 + 1 = (2 : ℕ) by decide, hz2]
    simp [F, ι, hz, hz']
  | more n ih₀ ih₁ =>
    calc
      _ = 2 * ((2 : ℤ[X]) ^ (n + 1) * F (n + 2)) +
          4 * X * ((2 : ℤ[X]) ^ n * F (n + 1)) := by
        dsimp only [F]
        rw [generalizedFibonacciPolynomial_add_two 0 1 1 X (n + 1)]
        simp only [pow_succ (2 : ℤ[X]) (n + 1), pow_succ (2 : ℤ[X]) n]
        ring
      _ = (z ^ (n + 3)).im := by
        rw [ih₀, ih₁]
        have hpow : z ^ (n + 3) = z ^ 2 * z ^ (n + 1) := by
          rw [← pow_add, show 2 + (n + 1) = n + 3 by omega]
        rw [hpow, hz2, add_mul, mul_assoc (ι (2 : ℤ[X])) z, ← pow_succ',
          QuadraticAlgebra.im_add, himul, himul]

private theorem coeff_rescale (p : ℤ[X]) (a : ℤ) (m : ℕ) :
    (p.comp (C a * X)).coeff m = a ^ m * p.coeff m := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [add_comp, coeff_add, hp, hq, mul_add]
  | monomial k b =>
    rw [← C_mul_X_pow_eq_monomial]
    simp only [mul_comp, C_comp, pow_comp, X_comp, mul_pow, ← C_pow, coeff_C_mul, coeff_X_pow]
    split_ifs with h
    · subst m; simp [mul_comm]
    · simp

private theorem coeff_four (j m : ℕ) :
    (((4 : ℤ[X]) * X + 1) ^ j).coeff m = (4 : ℤ) ^ m * (j.choose m : ℤ) := by
  have h := coeff_rescale ((X + 1 : ℤ[X]) ^ j) 4 m
  rw [pow_comp, add_comp, X_comp, one_comp, coeff_X_add_one_pow ℤ] at h
  simpa only [map_ofNat] using h

private theorem webb_parberry_of_polynomial {m n : ℕ} (hmn : m < n)
    (hpoly : (2 : ℤ[X]) ^ (n - 1) * generalizedFibonacciPolynomial 0 1 1 X n =
      ∑ j ∈ range ((n - 1) / 2 + 1), (n.choose (2 * j + 1) : ℤ[X]) * (4 * X + 1) ^ j) :
    ((n - m - 1).choose m : ℚ) = (2 : ℚ) ^ (2 * (m : ℤ) - n + 1) *
      ∑ j ∈ Icc m ((n - 1) / 2), (j.choose m : ℚ) * (n.choose (2 * j + 1) : ℚ) := by
  have hn : 1 ≤ n := by omega
  let u := (n - 1) / 2
  have hchoose (a : ℕ) : (a : ℤ[X]) = C (a : ℤ) := by simp
  have hcoeff : (generalizedFibonacciPolynomial 0 1 1 X n).coeff m =
      ((n - m - 1).choose m : ℤ) := by
    rw [gfp_fib_eq_sum_choose 1 X hn, finsetSum_coeff]
    simp only [one_pow, mul_one, hchoose, coeff_C_mul, coeff_X_pow]
    rw [sum_eq_single m]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · intro hm
      have hz : n - m - 1 < m := by
        simp only [mem_range, not_lt] at hm
        omega
      simp [Nat.choose_eq_zero_of_lt hz]
  have hsum : (∑ j ∈ Icc m u, (j.choose m : ℤ) * (n.choose (2 * j + 1) : ℤ)) =
      ∑ j ∈ range (u + 1), (j.choose m : ℤ) * (n.choose (2 * j + 1) : ℤ) := by
    apply sum_subset
    · intro j hj
      exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hj).2)
    · intro j hj hj'
      have hjm : j < m := by
        rw [mem_range] at hj
        rw [mem_Icc] at hj'
        omega
      simp [Nat.choose_eq_zero_of_lt hjm]
  have hInt : (2 : ℤ) ^ (n - 1) * ((n - m - 1).choose m : ℤ) =
      (4 : ℤ) ^ m * ∑ j ∈ Icc m u, (j.choose m : ℤ) * (n.choose (2 * j + 1) : ℤ) := by
    have hp := congrArg (fun p : ℤ[X] => p.coeff m) hpoly
    rw [show (2 : ℤ[X]) ^ (n - 1) = C ((2 : ℤ) ^ (n - 1)) by simp,
      coeff_C_mul, hcoeff, finsetSum_coeff] at hp
    rw [hsum, mul_sum, hp]
    apply sum_congr rfl
    intro j _
    rw [hchoose, coeff_C_mul, coeff_four]
    ac_rfl
  have hq : (2 : ℚ) ^ (n - 1) * ((n - m - 1).choose m : ℚ) =
      (4 : ℚ) ^ m * ∑ j ∈ Icc m u, (j.choose m : ℚ) * (n.choose (2 * j + 1) : ℚ) := by
    exact_mod_cast hInt
  have h2 : (2 : ℚ) ≠ 0 := by decide
  have h4 : (2 : ℚ) ^ (n - 1) * (2 : ℚ) ^ (2 * (m : ℤ) - n + 1) = (4 : ℚ) ^ m := by
    rw [← zpow_natCast (2 : ℚ) (n - 1), ← zpow_add₀ h2, Nat.cast_sub hn, Nat.cast_one]
    rw [show (n : ℤ) - 1 + (2 * (m : ℤ) - n + 1) = ((2 * m : ℕ) : ℤ) by push_cast; omega,
      zpow_natCast, pow_mul]
    rfl
  apply mul_left_cancel₀ (pow_ne_zero (n - 1) h2)
  rw [← mul_assoc, h4]
  exact hq

/-- **Webb–Parberry binomial identity.** For natural numbers $m < n$,
$$\binom{n-m-1}{m} = 2^{2m-n+1} \sum_{j=m}^{\lfloor (n-1)/2 \rfloor} \binom{j}{m} \binom{n}{2j+1},$$
an identity of rational numbers in which the exponent $2m-n+1$ may be negative.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Lemma 3.2 (1) (`fq-2024-florez11012023-lem-3.2`). -/
public theorem choose_sub_sub_one_eq_two_zpow_mul_sum {m n : ℕ} (hmn : m < n) :
    ((n - m - 1).choose m : ℚ) =
      (2 : ℚ) ^ (2 * (m : ℤ) - n + 1) *
        ∑ j ∈ Icc m ((n - 1) / 2), (j.choose m : ℚ) * (n.choose (2 * j + 1) : ℚ) := by
  apply webb_parberry_of_polynomial hmn
  have hn : n - 1 + 1 = n := by omega
  calc
    _ = ((ω + (1 : QuadraticAlgebra ℤ[X] (4 * X + 1) 0)) ^ n).im := by
      simpa only [hn] using webb_parberry_scaled (n - 1)
    _ = _ := webb_parberry_binomial_part n

end MetaMathlibExt

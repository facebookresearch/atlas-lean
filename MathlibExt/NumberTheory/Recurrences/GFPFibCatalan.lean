/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Sum
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-! # Catalan identity for Fibonacci-type generalized Fibonacci polynomials -/

namespace MetaMathlibExt

open Finset Polynomial
open scoped QuadraticAlgebra

namespace gfp_fib_catalan

/-- Only the odd powers of the formal square root contribute to the imaginary part. -/
private theorem im_pow_eq_sum {R : Type*} [CommRing R] (d D : R) (n : ℕ) :
    ((ω + algebraMap R (QuadraticAlgebra R D 0) d) ^ n).im =
      ∑ i ∈ range ((n - 1) / 2 + 1),
        (n.choose (2 * i + 1) : R) * d ^ (n - 2 * i - 1) * D ^ i := by
  let ι := algebraMap R (QuadraticAlgebra R D 0)
  have even_pow (i : ℕ) : (ω : QuadraticAlgebra R D 0) ^ (2 * i) = ι (D ^ i) := by
    rw [pow_mul, map_pow]
    congr 1
    simp [sq, QuadraticAlgebra.omega_mul_omega_eq_algebraMap, ι]
  cases n with
  | zero => simp
  | succ n =>
    rw [add_pow, ← QuadraticAlgebra.imₗ_apply, map_sum]
    symm
    refine sum_of_injOn (fun i ↦ 2 * i + 1) ?_ ?_ ?_ ?_
    · intro i _ j _ hij
      change 2 * i + 1 = 2 * j + 1 at hij
      omega
    · intro i hi
      simp only [SetLike.mem_coe, mem_range] at hi ⊢
      omega
    · intro k hk h
      obtain ⟨i, rfl | rfl⟩ := k.even_or_odd'
      · simp [even_pow, ι, ← map_pow]
      · exact (h ⟨i, mem_range.mpr (by have := mem_range.mp hk; omega), rfl⟩).elim
    · intro i _
      rw [show n + 1 - (2 * i + 1) = n + 1 - 2 * i - 1 by omega]
      simp [pow_succ ω (2 * i), even_pow, ι, ← map_pow]
      ring

end gfp_fib_catalan

/-- **Catalan identity for Fibonacci-type generalized Fibonacci polynomials.** Let $d$ and $g$ be
polynomials with integer coefficients, and let $F_n$ be the generalized Fibonacci polynomials
defined by $F_0 = 0$, $F_1 = 1$ and $F_{n+2} = d F_{n+1} + g F_n$. Then for every natural number
$n$ (for $n = 0$ both sides are $0$),
$$2^{n-1} F_n = \sum_{i=0}^{\lfloor (n-1)/2 \rfloor} \binom{n}{2i+1} d^{n-2i-1} (4g + d^2)^i.$$

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Theorem 3.3 (1) (`fq-2024-florez11012023-thm-3.3`). -/
public theorem gfp_fib_catalan (d g : ℤ[X]) (n : ℕ) :
    2 ^ (n - 1) * generalizedFibonacciPolynomial 0 1 d g n =
      ∑ i ∈ range ((n - 1) / 2 + 1),
        (n.choose (2 * i + 1) : ℤ[X]) * d ^ (n - 2 * i - 1) * (4 * g + d ^ 2) ^ i := by
  let D := 4 * g + d ^ 2
  let z := ω + algebraMap ℤ[X] (QuadraticAlgebra ℤ[X] D 0) d
  rw [← gfp_fib_catalan.im_pow_eq_sum]
  change _ = (z ^ n).im
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.succ_sub_one]
    induction n using Nat.twoStepInduction with
    | zero => simp [z]
    | one => simp [z, QuadraticAlgebra.im_mul, pow_succ, two_mul]
    | more n ih₀ ih₁ =>
      let F := generalizedFibonacciPolynomial 0 1 d g
      have hre : z.re = d := by simp [z]
      have him : z.im = 1 := by simp [z]
      calc
        _ = 2 * d * (2 ^ (n + 1) * F (n + 2)) + 4 * g * (2 ^ n * F (n + 1)) := by
          rw [show n + 2 + 1 = n + 1 + 2 by omega,
            generalizedFibonacciPolynomial_add_two]
          dsimp only [F]
          ring
        _ = (z ^ (n + 2 + 1)).im := by
          rw [ih₀, ih₁]
          simp only [pow_succ, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, hre, him, D]
          ring

end MetaMathlibExt

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

/-! # Catalan identity for Lucas-type generalized Fibonacci polynomials -/

namespace MetaMathlibExt

open Finset Polynomial
open scoped QuadraticAlgebra

namespace gfp_lucas_catalan

/-- In the binomial expansion of `(ω + d) ^ n`, exactly the even powers of the formal
square root can contribute to the real part. -/
private theorem re_pow_eq_sum {R : Type*} [CommRing R] (d D : R) (n : ℕ) :
    ((ω + algebraMap R (QuadraticAlgebra R D 0) d) ^ n).re =
      ∑ i ∈ range (n / 2 + 1), (n.choose (2 * i) : R) * d ^ (n - 2 * i) * D ^ i := by
  let ι := algebraMap R (QuadraticAlgebra R D 0)
  have even_pow (i : ℕ) : (ω : QuadraticAlgebra R D 0) ^ (2 * i) = ι (D ^ i) := by
    rw [pow_mul, map_pow]
    congr 1
    simp [sq, QuadraticAlgebra.omega_mul_omega_eq_algebraMap, ι]
  rw [add_pow, ← QuadraticAlgebra.reₗ_apply, map_sum]
  symm
  refine sum_of_injOn (fun i ↦ 2 * i) (mul_right_injective₀ (by decide : (2 : ℕ) ≠ 0)).injOn
    ?_ ?_ ?_
  · intro i hi
    simp only [SetLike.mem_coe, mem_range] at hi ⊢
    omega
  · intro k hk h
    obtain ⟨i, rfl | rfl⟩ := k.even_or_odd'
    · exact (h ⟨i, mem_range.mpr (by have := mem_range.mp hk; omega), rfl⟩).elim
    · simp [pow_succ ω (2 * i), even_pow, ι, ← map_pow]
  · intro i _
    simp [even_pow, ι, ← map_pow]
    ring

end gfp_lucas_catalan

/-- **Catalan identity for Lucas-type generalized Fibonacci polynomials.** Let $\alpha$ and $p_0$
be integers with $\alpha p_0 = 2$, let $p_1$ and $g$ be polynomials with integer coefficients, and
put $d = \alpha p_1$. Let $L_n$ be the generalized Fibonacci polynomials defined by $L_0 = p_0$,
$L_1 = p_1$ and $L_{n+2} = d L_{n+1} + g L_n$. Then for every natural number $n$,
$$2^n \alpha L_n = 2 \sum_{i=0}^{\lfloor n/2 \rfloor} \binom{n}{2i} d^{n-2i} (4g + d^2)^i.$$

Dividing both sides by $2$ gives the source's form, with $\alpha 2^{n-1} L_n$ on the left; the
factor $2$ is cleared so that $n = 0$ is included.

Source: Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas,
*Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024),
Article florez11012023, Theorem 3.3 (2) (`fq-2024-florez11012023-thm-3.3`). -/
public theorem gfp_lucas_catalan {α p₀ : ℤ} (hα : α * p₀ = 2) {p₁ d : ℤ[X]}
    (hd : d = C α * p₁) (g : ℤ[X]) (n : ℕ) :
    2 ^ n * C α * generalizedFibonacciPolynomial (C p₀) p₁ d g n =
      2 * ∑ i ∈ range (n / 2 + 1),
        (n.choose (2 * i) : ℤ[X]) * d ^ (n - 2 * i) * (4 * g + d ^ 2) ^ i := by
  let D := 4 * g + d ^ 2
  let z := ω + algebraMap ℤ[X] (QuadraticAlgebra ℤ[X] D 0) d
  rw [← gfp_lucas_catalan.re_pow_eq_sum]
  change _ = 2 * (z ^ n).re
  induction n using Nat.twoStepInduction with
  | zero => simpa using congrArg (C : ℤ →+* ℤ[X]) hα
  | one => simp [z, hd, mul_assoc]
  | more n ih₀ ih₁ =>
    let L := generalizedFibonacciPolynomial (C p₀) p₁ d g
    calc
      _ = 2 * d * (2 ^ (n + 1) * C α * L (n + 1)) +
          4 * g * (2 ^ n * C α * L n) := by
        rw [generalizedFibonacciPolynomial_add_two]
        dsimp only [L]
        ring
      _ = 2 * (z ^ (n + 2)).re := by
        rw [ih₀, ih₁]
        have hz : z.re = d := by simp [z]
        have hz' : z.im = 1 := by simp [z]
        simp only [pow_succ, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, hz, hz', D]
        ring

end MetaMathlibExt

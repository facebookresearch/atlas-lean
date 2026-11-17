/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Cast.Field

/-!
# The Dirichlet square of the von Mangoldt function

This file records divisor-sum identities for `Λ * Λ` and for the Möbius sums weighted by
squared logarithms, which are the algebraic input to Selberg's identity.

## Main statements

* `ArithmeticFunction.sum_divisors_moebius`: `∑_{d ∣ n} μ(d)` is `1` at `n = 1` and `0`
  otherwise, in any ring.
* `ArithmeticFunction.vonMangoldt_mul_vonMangoldt_apply`:
  `(Λ * Λ)(n) = Λ(n) log n + ∑_{d ∣ n} μ(d) log² d`.
* `ArithmeticFunction.sum_divisors_moebius_mul_log_div_sq`: the expansion of
  `∑_{d ∣ n} μ(d) log²(x / d)` in terms of `Λ` and `Λ * Λ`.
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace ArithmeticFunction

/-- The divisor sum of the Möbius function is the indicator of `n = 1`, in any ring. -/
theorem sum_divisors_moebius {R : Type*} [Ring R] (n : ℕ) :
    ∑ d ∈ n.divisors, (μ d : R) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction R => f n) (coe_moebius_mul_coe_zeta (R := R))
  simp only [coe_mul_zeta_apply, intCoe_apply, one_apply] at h
  exact h

/-- The Dirichlet square of the von Mangoldt function:
`(Λ * Λ)(n) = Λ(n) log n + ∑_{d ∣ n} μ(d) log² d`. -/
theorem vonMangoldt_mul_vonMangoldt_apply (n : ℕ) :
    (Λ * Λ) n = Λ n * Real.log n + ∑ d ∈ n.divisors, (μ d : ℝ) * Real.log d ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  set F : ArithmeticFunction ℝ := (μ : ArithmeticFunction ℝ).pmul log with hF
  have hFζ : F * (ζ : ArithmeticFunction ℝ) = -Λ := by
    ext m
    rw [coe_mul_zeta_apply, neg_apply, ← sum_moebius_mul_log_eq]
    simp [hF, pmul_apply]
  have hΛΛ : Λ * Λ = -(F * log) := by
    rw [← vonMangoldt_mul_zeta, ← mul_assoc, mul_comm F Λ, mul_assoc, hFζ]
    ring
  rw [hΛΛ, neg_apply, mul_apply, Nat.sum_divisorsAntidiagonal (fun i j => F i * log j),
    ← neg_neg (Λ n), ← sum_moebius_mul_log_eq, neg_mul, Finset.sum_mul,
    ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [hF, pmul_apply, log_apply, log_apply, intCoe_apply, Nat.cast_div hdn hd0,
    Real.log_div hn0 hd0]
  ring

/-- Expansion of the Möbius sum weighted by `log²(x / d)`: for `x ≠ 0`,
`∑_{d ∣ n} μ(d) log²(x / d) = [n = 1] log² x + 2 Λ(n) log x + (Λ * Λ)(n) - Λ(n) log n`. -/
theorem sum_divisors_moebius_mul_log_div_sq {x : ℝ} (hx : x ≠ 0) (n : ℕ) :
    ∑ d ∈ n.divisors, (μ d : ℝ) * Real.log (x / d) ^ 2
      = (if n = 1 then Real.log x ^ 2 else 0) + 2 * Λ n * Real.log x + (Λ * Λ) n
        - Λ n * Real.log n := by
  have hexp : ∑ d ∈ n.divisors, (μ d : ℝ) * Real.log (x / d) ^ 2
      = Real.log x ^ 2 * ∑ d ∈ n.divisors, (μ d : ℝ)
        - 2 * Real.log x * ∑ d ∈ n.divisors, (μ d : ℝ) * Real.log d
        + ∑ d ∈ n.divisors, (μ d : ℝ) * Real.log d ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
    rw [Real.log_div hx hd0]
    ring
  have hlog : ∑ d ∈ n.divisors, (μ d : ℝ) * Real.log d = -Λ n := by
    simpa [log_apply] using sum_moebius_mul_log_eq (n := n)
  rw [hexp, sum_divisors_moebius, hlog, vonMangoldt_mul_vonMangoldt_apply]
  split_ifs <;> ring

end ArithmeticFunction

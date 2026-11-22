/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Root lemmas for reciprocal sums of `m`th-order linear recursive sequences

This file proves the self-contained root lemmas of Du's paper on reciprocal sums and products of
`m`th-order linear recursive sequences.

## Main results

* `MetaMathlibExt.norm_le_one_of_aeval_eq_zero_of_monotone_coeff`: the Eneström–Kakeya theorem
  in monotone form. If a nonzero real polynomial `a₀ + a₁ x + ⋯ + aₙ xⁿ` of degree `n` satisfies
  `0 ≤ a₀ ≤ a₁ ≤ ⋯ ≤ aₙ`, then every complex root `z` satisfies `‖z‖ ≤ 1`.

## Proof

Multiplying by `1 - z` telescopes the polynomial:
`(1 - z) (a₀ + a₁ z + ⋯ + aₙ zⁿ) = a₀ + ∑_{i < n} (aᵢ₊₁ - aᵢ) zⁱ⁺¹ - aₙ zⁿ⁺¹`.
At a root `z` with `1 < ‖z‖`, the triangle inequality, the signs `0 ≤ a₀` and `0 ≤ aᵢ₊₁ - aᵢ`,
and `‖z‖ⁱ⁺¹ ≤ ‖z‖ⁿ` for `i < n` give
`aₙ ‖z‖ⁿ⁺¹ ≤ (a₀ + ∑_{i < n} (aᵢ₊₁ - aᵢ)) ‖z‖ⁿ = aₙ ‖z‖ⁿ`.
This is impossible: the leading coefficient `aₙ` is nonzero and at least `a₀ ≥ 0`, so `aₙ > 0`.
-/

open Polynomial

namespace MetaMathlibExt

/-- Multiplying `∑_{i ≤ n} bᵢ zⁱ` by `1 - z` telescopes it to
`b₀ + ∑_{i < n} (bᵢ₊₁ - bᵢ) zⁱ⁺¹ - bₙ zⁿ⁺¹`. -/
private theorem one_sub_mul_sum_range_mul_pow {R : Type*} [CommRing R] (b : ℕ → R) (z : R)
    (n : ℕ) :
    (1 - z) * ∑ i ∈ Finset.range (n + 1), b i * z ^ i =
      b 0 + ∑ i ∈ Finset.range n, (b (i + 1) - b i) * z ^ (i + 1) - b n * z ^ (n + 1) := by
  induction n with
  | zero =>
    rw [Finset.sum_range_one, Finset.sum_range_zero]
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih,
      Finset.sum_range_succ (fun i => (b (i + 1) - b i) * z ^ (i + 1))]
    ring

@[expose] public section

/-- **Eneström–Kakeya theorem.** Let $a_0 + a_1 x + \cdots + a_n x^n$ be a nonzero real
polynomial of degree $n$ with $0 \le a_0 \le a_1 \le \cdots \le a_n$. Then every complex root $z$
of this polynomial satisfies $|z| \le 1$.

Source: Tingting Du, *On the Reciprocal Sums and Products of m th-order Linear Recursive
Sequences*, Journal of Integer Sequences 27 (2024), Article 24.2.3, Lemma 3
(`jis-2024-24.2.3-lem-3`), quoted there as the Eneström–Kakeya theorem. -/
public theorem norm_le_one_of_aeval_eq_zero_of_monotone_coeff
    (p : ℝ[X]) (hp : p ≠ 0) (h0 : 0 ≤ p.coeff 0)
    (hmono : ∀ i < p.natDegree, p.coeff i ≤ p.coeff (i + 1))
    (z : ℂ) (hz : aeval z p = 0) : ‖z‖ ≤ 1 := by
  set n := p.natDegree
  set a := p.coeff
  have hd : ∀ i ∈ Finset.range n, 0 ≤ a (i + 1) - a i := fun i hi =>
    sub_nonneg.2 (hmono i (Finset.mem_range.1 hi))
  have htel : ∑ i ∈ Finset.range n, (a (i + 1) - a i) = a n - a 0 := Finset.sum_range_sub a n
  -- The leading coefficient is nonzero and at least `a 0 ≥ 0`.
  have han : 0 < a n := by
    have hne : a n ≠ 0 := leadingCoeff_ne_zero.2 hp
    have : 0 ≤ a n - a 0 := htel ▸ Finset.sum_nonneg hd
    exact lt_of_le_of_ne (by linarith) hne.symm
  refine not_lt.1 fun hlt => ?_
  have hsum : ∑ i ∈ Finset.range (n + 1), (a i : ℂ) * z ^ i = 0 := by
    rw [aeval_eq_sum_range] at hz
    simpa [Algebra.smul_def] using hz
  have hid := one_sub_mul_sum_range_mul_pow (fun i => (a i : ℂ)) z n
  rw [hsum, mul_zero] at hid
  have key : (a n : ℂ) * z ^ (n + 1) =
      (a 0 : ℂ) + ∑ i ∈ Finset.range n, ((a (i + 1) - a i : ℝ) : ℂ) * z ^ (i + 1) := by
    push_cast
    linear_combination hid
  have h1 : 1 ≤ ‖z‖ := hlt.le
  have hbound : a n * ‖z‖ ^ (n + 1) ≤ a n * ‖z‖ ^ n := by
    calc a n * ‖z‖ ^ (n + 1) = ‖(a n : ℂ) * z ^ (n + 1)‖ := by
          rw [norm_mul, norm_pow, Complex.norm_of_nonneg han.le]
      _ = ‖(a 0 : ℂ) + ∑ i ∈ Finset.range n, ((a (i + 1) - a i : ℝ) : ℂ) * z ^ (i + 1)‖ := by
          rw [key]
      _ ≤ ‖(a 0 : ℂ)‖ + ∑ i ∈ Finset.range n, ‖((a (i + 1) - a i : ℝ) : ℂ) * z ^ (i + 1)‖ :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
      _ = a 0 + ∑ i ∈ Finset.range n, (a (i + 1) - a i) * ‖z‖ ^ (i + 1) := by
          rw [Complex.norm_of_nonneg h0]
          congr 1
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [norm_mul, norm_pow, Complex.norm_of_nonneg (hd i hi)]
      _ ≤ a 0 * ‖z‖ ^ n + ∑ i ∈ Finset.range n, (a (i + 1) - a i) * ‖z‖ ^ n := by
          gcongr with i hi
          · exact le_mul_of_one_le_right h0 (one_le_pow₀ h1)
          · exact hd i hi
          · exact Finset.mem_range.1 hi
      _ = a n * ‖z‖ ^ n := by rw [← Finset.sum_mul, htel]; ring
  have h2 : ‖z‖ ^ (n + 1) ≤ ‖z‖ ^ n := le_of_mul_le_mul_left hbound han
  have h3 : ‖z‖ ^ n < ‖z‖ ^ (n + 1) := pow_lt_pow_right₀ hlt (Nat.lt_succ_self n)
  linarith

end

end MetaMathlibExt

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.RamanujanSigma

import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Tests for Ramanujan's formula for `∑ σ_a(n) σ_b(n) n^{-s}`

A concrete value (`∑ d(n)² n⁻² = 5π⁴/72`), the convolution identity at a prime power, and
instantiations of the twisted formulas.
-/

@[expose] public section

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace RamanujanSigmaTest

/-- `∑ d(n)² / n² = ζ(2)⁴ / ζ(4) = 5 π⁴ / 72`. -/
example : LSeries (fun n ↦ ((σ 0 n : ℕ) : ℂ) ^ 2) 2 = 5 * (Real.pi : ℂ) ^ 4 / 72 := by
  rw [LSeries_sigma_zero_sq (by norm_num), show (2 : ℂ) * 2 = 4 by norm_num, riemannZeta_two,
    riemannZeta_four]
  have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

/-- Dirichlet convolution at `p ^ 2`. -/
example (f g : ArithmeticFunction ℤ) :
    (f * g) (2 ^ 2) = f 1 * g 4 + f 2 * g 2 + f 4 * g 1 := by
  rw [mul_apply_prime_pow f g Nat.prime_two 2]
  simp [Finset.sum_range_succ]

/-- The four-parameter identity with `α = γ = 1`, `β = δ = 0`: `∑ Tⁿ = 1 / (1 - T)`. -/
example {T : ℝ} (hT : ‖T‖ < 1) : HasSum (fun n : ℕ ↦ T ^ n) (1 / (1 - T)) := by
  have h := MetaMathlibExt.hasSum_ramanujan_four_param (α := (1 : ℝ)) (β := 0) (γ := 1) (δ := 0)
    (T := T) one_ne_zero one_ne_zero (by simpa using hT) (by simp) (by simp) (by simp)
  have h1 : (1 : ℝ) - T ≠ 0 := by
    intro h0; rw [show T = 1 by linarith] at hT; simp at hT
  convert h using 1
  · funext n; simp
  · field_simp
    ring

/-- Ramanujan's formula at `a = b = 0` recovers `ζ⁴(s)/ζ(2s)`. -/
example {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n ↦ sigmaR 0 n * sigmaR 0 n) s =
      riemannZeta s ^ 4 / riemannZeta (2 * s) := by
  rw [LSeries_sigmaR_mul_sigmaR hs (by simpa using hs) (by simpa using hs) (by simpa using hs)]
  simp only [sub_zero]
  ring

/-- The twisted formula for the trivial character mod `1` recovers the untwisted one. -/
example {a b s : ℂ} (hs : 1 < s.re) (hsa : 1 < (s - a).re) (hsb : 1 < (s - b).re)
    (hsab : 1 < (s - a - b).re) :
    LSeries (fun n ↦ (1 : DirichletCharacter ℂ 1).sigmaR a n *
        (1 : DirichletCharacter ℂ 1).sigmaR b n) s =
      riemannZeta s * LSeries (fun n ↦ (1 : DirichletCharacter ℂ 1) n) (s - a) *
        LSeries (fun n ↦ (1 : DirichletCharacter ℂ 1) n) (s - b) *
        LSeries (fun n ↦ ((1 : DirichletCharacter ℂ 1) * 1) n) (s - a - b) /
        LSeries (fun n ↦ ((1 : DirichletCharacter ℂ 1) * 1) n) (2 * s - a - b) :=
  DirichletCharacter.LSeries_sigmaR_mul_sigmaR 1 1 hs hsa hsb hsab

end RamanujanSigmaTest

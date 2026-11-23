/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_jacobiTheta_two_eq_tprod.lean`
and
`P2M/Sol/S_jacobiTheta_two_eq_tprod.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import MathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct

@[expose] public section

open Complex
open scoped Real

/-- Jacobi's triple product in the `jacobiTheta₂` normalisation: for
`0 < im τ`, `jacobiTheta₂ z τ` is the product over `n : ℕ` of
`(1 - exp (2πi(n+1)τ)) (1 + exp (πi(2n+1)τ + 2πiz))
(1 + exp (πi(2n+1)τ - 2πiz))`. -/
public theorem jacobiTheta₂_eq_tprod (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiTheta₂ z τ = ∏' n : ℕ,
      ((1 - Complex.exp (2 * π * I * (n + 1) * τ)) *
        (1 + Complex.exp (π * I * (2 * n + 1) * τ + 2 * π * I * z)) *
        (1 + Complex.exp (π * I * (2 * n + 1) * τ - 2 * π * I * z))) := by
  set Q : ℂ := Complex.exp (π * I * τ) with hQdef
  set Z : ℂ := Complex.exp (2 * π * I * z) with hZdef
  have hZne : Z ≠ 0 := Complex.exp_ne_zero _
  have hQ : ‖Q‖ < 1 := by
    rw [hQdef, Complex.norm_exp]
    have hre : (π * I * τ).re = -π * τ.im := by
      simp [Complex.mul_re, Complex.mul_im, Real.pi_pos.le]
    rw [hre, Real.exp_lt_one_iff]
    have hpi : (0 : ℝ) < π := Real.pi_pos
    nlinarith
  have htriple :=
    (MetaMathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct.jacobi_triple_product
      Z Q hZne hQ).2.2
  have hterm : ∀ n : ℤ, Z ^ n * Q ^ (n * n).toNat = jacobiTheta₂_term n z τ := by
    intro n
    have hnn : (0 : ℤ) ≤ n * n := mul_self_nonneg n
    have hcast : (((n * n).toNat : ℕ) : ℂ) = (n : ℂ) * (n : ℂ) := by
      have h1 : (((n * n).toNat : ℕ) : ℤ) = n * n := Int.toNat_of_nonneg hnn
      have h2 : (((n * n).toNat : ℕ) : ℂ) = ((n * n : ℤ) : ℂ) := by
        rw [← h1]; rfl
      rw [h2]; push_cast; ring
    unfold jacobiTheta₂_term
    rw [hZdef, hQdef, ← Complex.exp_int_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    rw [hcast]
    ring
  have hsum : (∑' n : ℤ, Z ^ n * Q ^ (n * n).toNat) = jacobiTheta₂ z τ := by
    rw [jacobiTheta₂]
    exact tsum_congr hterm
  have hfac : ∀ n : ℕ,
      (1 - Q ^ (2 * n + 2)) * (1 + Z * Q ^ (2 * n + 1)) *
          (1 + Z⁻¹ * Q ^ (2 * n + 1)) =
        (1 - Complex.exp (2 * π * I * (n + 1) * τ)) *
          (1 + Complex.exp (π * I * (2 * n + 1) * τ + 2 * π * I * z)) *
          (1 + Complex.exp (π * I * (2 * n + 1) * τ - 2 * π * I * z)) := by
    intro n
    have e1 : Q ^ (2 * n + 2) = Complex.exp (2 * π * I * (n + 1) * τ) := by
      rw [hQdef, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have e2 : Z * Q ^ (2 * n + 1) =
        Complex.exp (π * I * (2 * n + 1) * τ + 2 * π * I * z) := by
      rw [hZdef, hQdef, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have e3 : Z⁻¹ * Q ^ (2 * n + 1) =
        Complex.exp (π * I * (2 * n + 1) * τ - 2 * π * I * z) := by
      have hinv : Z⁻¹ = Complex.exp (-(2 * π * I * z)) := by
        rw [hZdef, ← Complex.exp_neg]
      rw [hinv, hQdef, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [e1, e2, e3]
  rw [← hsum, htriple]
  exact tprod_congr hfac

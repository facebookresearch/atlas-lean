/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The product formula for the lattice discriminant

We identify the lattice invariants for the periods `(1, τ)` with the normalized Eisenstein
series and apply Mathlib's identities for the modular discriminant.
-/

namespace MetaMathlibExt

open EisensteinSeries ModularForm
open scoped UpperHalfPlane Real

/-- **Jacobi's product formula for the discriminant of a lattice.** For `τ` in the upper
half-plane, take `g₂` to be sixty times the sum of the inverse fourth powers of the nonzero
periods `a * τ + b`, and `g₃` to be one hundred forty times the sum of the inverse sixth powers.
The displayed sums include the zero pair, whose summand in Lean is zero. Then `g₂³ - 27 * g₃²`
is `(2π)¹²` times both `η(τ)²⁴` and `q * ∏_{n ≥ 1} (1 - qⁿ)²⁴`, where `q = exp (2πiτ)`.

Source: C. L. Siegel, *Lectures on Advanced Analytic Number Theory*, Chapter 1, §2, p. 14. -/
public theorem lattice_discriminant_eq_eta_product (τ : ℍ) :
    let g₂ : ℂ := 60 * ∑' v : Fin 2 → ℤ, (((v 0 : ℂ) * τ + v 1) ^ 4)⁻¹
    let g₃ : ℂ := 140 * ∑' v : Fin 2 → ℤ, (((v 0 : ℂ) * τ + v 1) ^ 6)⁻¹
    let q := Complex.exp (2 * π * Complex.I * τ)
    g₂ ^ 3 - 27 * g₃ ^ 2 = (2 * π : ℂ) ^ 12 * eta τ ^ 24 ∧
      g₂ ^ 3 - 27 * g₃ ^ 2 = (2 * π : ℂ) ^ 12 * (q * ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24) := by
  have h₄ : (∑' v : Fin 2 → ℤ, (((v 0 : ℂ) * τ + v 1) ^ 4)⁻¹) =
      riemannZeta 4 * (2 * E₄ τ) := by
    have h := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries (k := 4) (by decide) τ
    have hE : E₄ τ = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 4 τ := rfl
    simpa only [eisSummand, Nat.cast_ofNat, zpow_neg, zpow_ofNat, hE, ← mul_assoc,
      show (2 : ℂ) * (1 / 2) = 1 by norm_num, one_mul] using h
  have h₆ : (∑' v : Fin 2 → ℤ, (((v 0 : ℂ) * τ + v 1) ^ 6)⁻¹) =
      riemannZeta 6 * (2 * E₆ τ) := by
    have h := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries (k := 6) (by decide) τ
    have hE : E₆ τ = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 6 τ := rfl
    simpa only [eisSummand, Nat.cast_ofNat, zpow_neg, zpow_ofNat, hE, ← mul_assoc,
      show (2 : ℂ) * (1 / 2) = 1 by norm_num, one_mul] using h
  have zeta_six : riemannZeta 6 = (π : ℂ) ^ 6 / 945 := by
    have hB : bernoulli 6 = 1 / 42 := by decide +kernel
    have h := (hasSum_zeta_nat (k := 3) (by decide)).tsum_eq
    norm_num at h
    rw [hB] at h
    have h' : (∑' n : ℕ, 1 / (n : ℝ) ^ 6) = π ^ 6 / 945 := by
      simp_rw [one_div]
      rw [h]
      push_cast
      ring
    convert congr(($h' : ℂ)) using 1
    · rw [show (6 : ℂ) = (6 : ℕ) by norm_num, zeta_nat_eq_tsum_of_gt_one (by decide : 1 < 6)]
      simp [push_cast]
    · norm_cast
  dsimp only
  rw [h₄, h₆, riemannZeta_four, zeta_six]
  have hΔ := discriminant_eq_E₄_cube_sub_E₆_sq τ
  change eta τ ^ 24 = _ at hΔ
  have hprod := discriminant_eq_q_prod τ
  change eta τ ^ 24 = _ at hprod
  have hmain : (60 * ((π : ℂ) ^ 4 / 90 * (2 * E₄ τ))) ^ 3 -
      27 * (140 * ((π : ℂ) ^ 6 / 945 * (2 * E₆ τ))) ^ 2 =
        (2 * π : ℂ) ^ 12 * eta τ ^ 24 := by
    rw [hΔ]
    ring
  refine ⟨hmain, hmain.trans ?_⟩
  congr 1
  simpa [Function.Periodic.qParam, eta_q_eq_pow] using hprod

end MetaMathlibExt

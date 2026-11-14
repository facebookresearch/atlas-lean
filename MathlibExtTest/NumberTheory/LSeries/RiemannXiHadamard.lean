/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.RiemannXiHadamard
import MathlibExt.NumberTheory.LSeries.RiemannXiZeros

/-!
# Tests for the Hadamard product of the Riemann `ξ` function

The enumeration hypothesis `∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w` used by
the Hadamard product, the zero-sum expansion of `-ζ'/ζ` and the explicit formulas is
satisfiable: `RiemannXi.exists_card_eq_analyticOrderAt` supplies a family, and the theorems can be
instantiated at it.
-/

@[expose] public section

open RiemannXi ComplexConjugate

namespace RiemannXiHadamardTest

example : riemannXi 0 = 1 / 2 := riemannXi_zero

example : riemannXi 1 = 1 / 2 := riemannXi_one

example (s : ℂ) : riemannXi (conj s) = conj (riemannXi s) := riemannXi_conj s

/-- `ξ` has order exactly `1`. -/
example : Complex.HasGrowthOrder riemannXi 1 := hasGrowthOrder_riemannXi

/-- `ζ` has infinitely many nontrivial zeros. -/
example : riemannZetaNontrivialZeros.Infinite := riemannZetaNontrivialZeros_infinite

/-- The Hadamard product can be instantiated at an actual enumeration of the zeros. -/
example : ∃ (ι : Type) (z : ι → ℂ) (A B : ℂ), ∀ s, riemannXi s =
    Complex.exp (A + B * s) * ∏' n, (1 - s / z n) * Complex.exp (s / z n) := by
  obtain ⟨ι, z, hz⟩ := exists_card_eq_analyticOrderAt
  obtain ⟨A, B, h⟩ := exists_riemannXi_eq_exp_mul_tprod hz
  exact ⟨ι, z, A, B, h⟩

/-- The constants of the Hadamard product: `A ≡ -log 2 (mod 2πi)` and `∑ Re (1/ρ) = -Re B`. -/
example : ∃ (ι : Type) (z : ι → ℂ) (A B : ℂ),
    (∃ k : ℤ, A = -(Real.log 2 : ℂ) + 2 * Real.pi * Complex.I * k) ∧
      HasSum (fun n => (1 / z n).re) (-B.re) := by
  obtain ⟨ι, z, hz⟩ := exists_card_eq_analyticOrderAt
  obtain ⟨A, B, h⟩ := exists_riemannXi_eq_exp_mul_tprod hz
  exact ⟨ι, z, A, B, exists_eq_neg_log_two_of_riemannXi_eq_exp_mul_tprod h,
    hasSum_re_one_div_of_riemannXi_eq_exp_mul_tprod hz h⟩

/-- The zero-sum expansion of `-ζ'/ζ` at `s = 2`. -/
example : ∃ (ι : Type) (z : ι → ℂ) (B : ℂ),
    -logDeriv riemannZeta 2 = 1 / (2 - 1) - B - (Real.log Real.pi : ℂ) / 2
      + Complex.digamma (2 / 2 + 1) / 2 - ∑' n, (1 / (2 - z n) + 1 / z n) := by
  obtain ⟨ι, z, hz⟩ := exists_card_eq_analyticOrderAt
  obtain ⟨A, B, h⟩ := exists_riemannXi_eq_exp_mul_tprod hz
  exact ⟨ι, z, B, neg_logDeriv_riemannZeta_eq hz h (by norm_num)
    (riemannZeta_ne_zero_of_one_le_re (by norm_num))⟩

/-- An enumeration consists of nonzero points with `∑ ‖ρ‖⁻² < ∞`. -/
example {ι : Type*} {z : ι → ℂ}
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w) :
    (∀ n, z n ≠ 0) ∧ Summable fun n => ‖z n‖ ^ (-2 : ℝ) :=
  ⟨ne_zero_of_card_eq_analyticOrderAt hz, summable_norm_rpow_neg_two hz⟩

end RiemannXiHadamardTest

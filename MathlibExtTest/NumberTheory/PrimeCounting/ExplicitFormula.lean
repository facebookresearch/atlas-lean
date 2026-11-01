/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.ExplicitFormula

/-!
# Tests for the explicit formula for `ψ(x)` and von Koch's criterion

The explicit formula instantiated at an actual enumeration of the zeros of `ξ`, at `x = 3/2`
(where `ψ(x) = 0`) and at `x = 7/3`, which is not a half-integer; the truncated formula; and the
two directions of von Koch's criterion.
-/

@[expose] public section

open Filter Topology RiemannXi

namespace ExplicitFormulaTest

/-- At `x = 3/2`, `ψ(x) = 0`, so the zero sum converges to
`3/2 - ζ'(0)/ζ(0) - ½ log (1 - 4/9)`. -/
example : ∃ (ι : Type) (z : ι → ℂ),
    Tendsto (fun R : ℝ => ∑' n, (if |(z n).im| < R then ((3 / 2 : ℝ) : ℂ) ^ z n / z n else 0))
      atTop (𝓝 (((3 / 2 : ℝ) : ℂ) - deriv riemannZeta 0 / riemannZeta 0 -
        (1 / 2 : ℂ) * (Real.log (1 - (3 / 2 : ℝ) ^ (-2 : ℤ)) : ℂ))) := by
  obtain ⟨ι, z, hz⟩ := exists_card_eq_analyticOrderAt
  refine ⟨ι, z, ?_⟩
  have h := tendsto_sum_cpow_div_zeros_explicit_formula z hz (x := 3 / 2) (by norm_num)
    fun n hn => by
      have h2 : (2 * n : ℝ) = 3 := by rw [hn]; norm_num
      have h3 : 2 * n = 3 := by exact_mod_cast h2
      omega
  rwa [Chebyshev.psi_eq_zero_of_lt_two (by norm_num), Complex.ofReal_zero, sub_zero] at h

/-- The explicit formula holds at every `x > 1` that is not a prime power, here `x = 7/3`. -/
example : ∃ (ι : Type) (z : ι → ℂ),
    Tendsto (fun R : ℝ => ∑' n, (if |(z n).im| < R then ((7 / 3 : ℝ) : ℂ) ^ z n / z n else 0))
      atTop (𝓝 (((7 / 3 : ℝ) : ℂ) - deriv riemannZeta 0 / riemannZeta 0 -
        (1 / 2 : ℂ) * (Real.log (1 - (7 / 3 : ℝ) ^ (-2 : ℤ)) : ℂ) -
          (Chebyshev.psi (7 / 3) : ℂ))) := by
  obtain ⟨ι, z, hz⟩ := exists_card_eq_analyticOrderAt
  refine ⟨ι, z, tendsto_sum_cpow_div_zeros_explicit_formula z hz (by norm_num) fun n hn => ?_⟩
  have h3 : (3 * n : ℝ) = 7 := by rw [hn]; norm_num
  have h : 3 * n = 7 := by exact_mod_cast h3
  omega

/-- The truncated explicit formula is instantiable. -/
example : ∃ C T₀ : ℝ, ∀ T ≥ T₀, ∃ R : ℝ, |R - T| ≤ 1 ∧ ∃ (ι : Type) (z : ι → ℂ),
    ‖(Chebyshev.psi (5 / 2) : ℂ) - ((5 / 2 : ℝ) : ℂ) +
        ∑' n, (if |(z n).im| < R then ((5 / 2 : ℝ) : ℂ) ^ z n / z n else 0) +
        deriv riemannZeta 0 / riemannZeta 0 +
        (1 / 2 : ℂ) * (Real.log (1 - (5 / 2 : ℝ) ^ (-2 : ℤ)) : ℂ)‖
      ≤ C * ((5 / 2) * Real.log (5 / 2) ^ 2 / R +
        (5 / 2) * Real.log R ^ 2 / (R * Real.log (5 / 2))) := by
  obtain ⟨C, T₀, h⟩ := exists_truncated_explicit_formula_chebyshevPsi.{0}
  refine ⟨C, T₀, fun T hT => ?_⟩
  obtain ⟨R, hR, hR'⟩ := h T hT
  obtain ⟨ι, z, hz⟩ := exists_card_eq_analyticOrderAt
  exact ⟨R, hR, ι, z, hR' z hz (5 / 2) ⟨2, two_pos, by norm_num⟩⟩

/-- Perron's formula for `ψ(x)` at `x = 5/2`, on the line `Re s = 2`. -/
example : Tendsto (fun R : ℝ => (1 / (2 * Real.pi) : ℂ) * ∫ t in (-R)..R,
      -(deriv riemannZeta ((2 : ℝ) + t * Complex.I) / riemannZeta ((2 : ℝ) + t * Complex.I)) *
        (((5 / 2 : ℝ) : ℂ) ^ ((2 : ℝ) + t * Complex.I) / ((2 : ℝ) + t * Complex.I))) atTop
    (𝓝 (Chebyshev.psi (5 / 2) : ℂ)) :=
  tendsto_truncated_integral_chebyshevPsi (by norm_num) (fun n hn => by
    have h2 : (2 * n : ℝ) = 5 := by rw [hn]; norm_num
    have h3 : 2 * n = 5 := by exact_mod_cast h2
    omega) one_lt_two

/-- **Von Koch's criterion** uses Mathlib's `RiemannHypothesis`. -/
example : RiemannHypothesis ↔ (fun x : ℝ => Chebyshev.psi x - x) =O[atTop]
    (fun x : ℝ => Real.sqrt x * Real.log x ^ 2) :=
  riemannHypothesis_iff_chebyshevPsi_sub_self_isBigO

example (hRH : RiemannHypothesis) : (fun x : ℝ => Chebyshev.psi x - x) =O[atTop]
    (fun x : ℝ => Real.sqrt x * Real.log x ^ 2) :=
  chebyshevPsi_sub_self_isBigO_of_riemannHypothesis hRH

end ExplicitFormulaTest

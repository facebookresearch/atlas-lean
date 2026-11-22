/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.PowerSeries.Expand
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
public import WantedExt.NumberTheory.SquaresTriangularRepresentationsWanted

/-!
# Ramanujan's theta functions, the Rogers-Ramanujan continued fraction and the golden ratio

Statements from S. E. Gladun and M. P. Chaudhary, *Connecting Ramanujan's Theta Functions, the
Rogers-Ramanujan Continued Fraction, and the Golden Ratio*, INTEGERS 25 (2025), Article A43.

`ψ(q) = ∑_{n ≥ 0} q^{n(n+1)/2}` and the coefficient
`g(0) = (16ψ⁵(q) - τ(q){τ⁴(q) + 5τ²(q)ρ(q) + 5ρ²(q)}) / (5ψ(q⁵))`, with
`τ(q) = ψ(q) - 5q³ψ(q²⁵)` and `ρ(q) = ψ²(q) - 5qψ²(q⁵)`. Theorem 1 is stated on the imaginary
axis `τ = it`, `t > 0`, where `q = e^{πiτ} = e^{-πt}` and `q' = e^{-π/t}` are real in `(0, 1)`
and every power is a positive real power. Theorem 2 is stated as an identity of integer power
series (`ψ` is `triangularThetaSeries`, `(q^k; q^k)_∞` is `qEulerProduct k`, `q ↦ q^k` is
`PowerSeries.expand k`), with the denominators `5ψ(q⁵)`, `E₅` and `E₂₅` cleared.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- The Rogers-Ramanujan continued fraction for real `0 ≤ x < 1`, through its product formula
`R(x) = x^{1/5} (x; x⁵)_∞ (x⁴; x⁵)_∞ / ((x²; x⁵)_∞ (x³; x⁵)_∞)` with the positive real fifth
root.

Source: S. E. Gladun and M. P. Chaudhary, *Connecting Ramanujan's Theta Functions, the
Rogers-Ramanujan Continued Fraction, and the Golden Ratio*, INTEGERS 25 (2025), Article A43,
Section 1 (the Rogers-Ramanujan continued fraction formula). -/
public noncomputable def rogersRamanujanContFracReal (x : ℝ) : ℝ :=
  x ^ (1 / 5 : ℝ) * ∏' n : ℕ, ((1 - x ^ (5 * n + 1)) * (1 - x ^ (5 * n + 4)) /
    ((1 - x ^ (5 * n + 2)) * (1 - x ^ (5 * n + 3))))

/-- `R(0) = 0`.

Source: S. E. Gladun and M. P. Chaudhary, *Connecting Ramanujan's Theta Functions, the
Rogers-Ramanujan Continued Fraction, and the Golden Ratio*, INTEGERS 25 (2025), Article A43,
Section 1 (the Rogers-Ramanujan continued fraction formula). -/
public theorem rogersRamanujanContFracReal_zero : rogersRamanujanContFracReal 0 = 0 := by
  simp [rogersRamanujanContFracReal]

/-- Theorem 1 on the imaginary axis: for `τ = it` with `t > 0`, put `q = e^{πiτ} = e^{-πt}` and
`q' = e^{πiτ'} = e^{-π/t}` (`ττ' = -1`). With `Φ = (√5 + 1)/2`,
`U = {R(q) R(q'^{4/5})}^{5/2}` and `V = {R(q) / R(q'^{4/5})}^{5/2}`,
`(√Φ - 1/√Φ)(U + 1/U) + (√Φ + 1/√Φ)(V - 1/V) = g(0) / (√q {(q; q)_∞ (q⁵; q⁵)_∞}²)`.

Source: S. E. Gladun and M. P. Chaudhary, *Connecting Ramanujan's Theta Functions, the
Rogers-Ramanujan Continued Fraction, and the Golden Ratio*, INTEGERS 25 (2025), Article A43,
Theorem 1, Equation (3) (`integers-2025-A43-thm-1`). -/
public theorem_wanted rogersRamanujan_golden_ratio_theta_relation (t : ℝ) (ht : 0 < t) :
    let q : ℝ := Real.exp (-Real.pi * t)
    let q' : ℝ := Real.exp (-Real.pi / t)
    let ψ : ℝ → ℝ := fun x => ∑' n : ℕ, x ^ (n * (n + 1) / 2)
    let E : ℝ → ℝ := fun x => ∏' n : ℕ, (1 - x ^ (n + 1))
    let τ : ℝ := ψ q - 5 * q ^ 3 * ψ (q ^ 25)
    let ρ : ℝ := ψ q ^ 2 - 5 * q * ψ (q ^ 5) ^ 2
    let g₀ : ℝ := (16 * ψ q ^ 5 - τ * (τ ^ 4 + 5 * τ ^ 2 * ρ + 5 * ρ ^ 2)) / (5 * ψ (q ^ 5))
    let Φ : ℝ := (Real.sqrt 5 + 1) / 2
    let R₁ : ℝ := rogersRamanujanContFracReal q
    let R₂ : ℝ := rogersRamanujanContFracReal (q' ^ (4 / 5 : ℝ))
    let U : ℝ := (R₁ * R₂) ^ (5 / 2 : ℝ)
    let V : ℝ := (R₁ / R₂) ^ (5 / 2 : ℝ)
    (Real.sqrt Φ - 1 / Real.sqrt Φ) * (U + 1 / U) +
        (Real.sqrt Φ + 1 / Real.sqrt Φ) * (V - 1 / V) =
      1 / Real.sqrt q * (g₀ / (E q * E (q ^ 5)) ^ 2)

/-- Theorem 2 with denominators cleared: with `E_k = (q^k; q^k)_∞` and `g(0)` as above,
`g(0) = E₅⁵/E₂₅ + 20q E₁⁴E₂₅/E₅ + 110q² E₁³E₂₅²/E₅ + 350q³ E₁²E₂₅³/E₅ + 600q⁴ E₁E₂₅⁴/E₅
+ 625q⁵ E₂₅⁵/E₅`, multiplied through by `5ψ(q⁵) E₅ E₂₅`, as integer power series.

Source: S. E. Gladun and M. P. Chaudhary, *Connecting Ramanujan's Theta Functions, the
Rogers-Ramanujan Continued Fraction, and the Golden Ratio*, INTEGERS 25 (2025), Article A43,
Theorem 2 (`integers-2025-A43-thm-2`). -/
public theorem_wanted rogersRamanujan_theta_coeff_eta_quotient :
    let ψ : ℤ⟦X⟧ := triangularThetaSeries
    let τ : ℤ⟦X⟧ := ψ - 5 * X ^ 3 * expand 25 (by norm_num) ψ
    let ρ : ℤ⟦X⟧ := ψ ^ 2 - 5 * X * expand 5 (by norm_num) ψ ^ 2
    (16 * ψ ^ 5 - τ * (τ ^ 4 + 5 * τ ^ 2 * ρ + 5 * ρ ^ 2)) * qEulerProduct 5 * qEulerProduct 25 =
      5 * expand 5 (by norm_num) ψ *
        (qEulerProduct 5 ^ 6 + qEulerProduct 25 *
          (20 * X * qEulerProduct 1 ^ 4 * qEulerProduct 25 +
            110 * X ^ 2 * qEulerProduct 1 ^ 3 * qEulerProduct 25 ^ 2 +
            350 * X ^ 3 * qEulerProduct 1 ^ 2 * qEulerProduct 25 ^ 3 +
            600 * X ^ 4 * qEulerProduct 1 * qEulerProduct 25 ^ 4 +
            625 * X ^ 5 * qEulerProduct 25 ^ 5))

end

end MetaMathlibExt

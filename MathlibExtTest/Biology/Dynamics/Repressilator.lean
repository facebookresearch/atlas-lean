/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.Repressilator
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Tests for the repressilator: the Hopf point of the `n = 4` model (`α = 2`, equilibrium
`(1, 1, 1)`, eigenvalues `-3, ±i√3`, period `2π/√3`, periodic orbits from the Hopf theorem), a
parameter set below the Hopf point (stable) and one above it (unstable), and the `n = 2` model,
which has no Hopf point. Parameter values (equilibria, loop gains) are computed from the
definitions. -/

open Polynomial Real

namespace MathlibExtTest.Biology.Dynamics.Repressilator

open MathlibExt.Biology.Dynamics.Repressilator

/-! ### The Hopf point of the `n = 4` model: `α = 2`, `p = 1` -/

/-- The critical rate: `eqRate 4 1 = 1 · (1 + 1⁴) = 2`. -/
example : eqRate 4 1 = 2 := by norm_num [eqRate]

/-- `(1, 1, 1)` is an equilibrium of `ẋᵢ = 2 / (1 + xᵢ₋₁⁴) - xᵢ`, computed from the
definition. -/
example : vectorField 4 2 (fun _ => 1) = 0 := by
  funext i; norm_num [vectorField]

/-- The field is not identically zero: at the origin it is `(2, 2, 2)`. -/
example : vectorField 4 2 (fun _ => 0) = fun _ => 2 := by
  funext i; norm_num [vectorField]

/-- It is the only nonnegative equilibrium for `α = 2`. -/
example (x : Fin 3 → ℝ) (hx : ∀ j, 0 ≤ x j) (h : vectorField 4 2 x = 0) : x = fun _ => 1 :=
  eq_const_of_vectorField_eq_zero (by norm_num) (by norm_num) zero_le_one
    (by norm_num [eqRate]) hx h

/-- The positive equilibrium level for `α = 2` is unique (it is `1` by `eqRate 4 1 = 2`). -/
example : ∃! p : ℝ, 0 < p ∧ eqRate 4 p = 2 := existsUnique_eqLevel 4 (by norm_num)

/-- The loop gain at the critical level is `4 · 1 / (1 + 1) = 2`, from the definition. -/
example : gain 4 1 = 2 := by norm_num [gain]

/-- The Hopf level from `gain_eq_two_iff`: `pⁿ = 2 / (n - 2) = 1`. -/
example : gain 4 1 = 2 ↔ (1 : ℝ) ^ 4 = 2 / ((4 : ℕ) - 2) :=
  gain_eq_two_iff (by norm_num) zero_le_one

/-- The Jacobian at `(1, 1, 1)` has `-1` on the diagonal and `-2` at `(i, i - 1)`. -/
example : LinearMap.toMatrix' (fderiv ℝ (vectorField 4 (eqRate 4 1)) (fun _ => 1) :
    (Fin 3 → ℝ) →ₗ[ℝ] Fin 3 → ℝ) = !![-1, 0, -2; -2, -1, 0; 0, -2, -1] := by
  rw [toMatrix'_fderiv_vectorField 4 zero_le_one, show gain 4 1 = 2 by norm_num [gain]]
  ext i j
  fin_cases i <;> fin_cases j <;> simp (config := { decide := true }) [jacobian]

/-- The characteristic polynomial at the Hopf point is `(λ + 1)³ + 8`. -/
example : linCharpoly (vectorField 4 (eqRate 4 1)) (fun _ => 1) = (X + 1) ^ 3 + C 8 := by
  rw [linCharpoly_vectorField 4 zero_le_one, show gain 4 1 = 2 by norm_num [gain],
    charpoly_jacobian]
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
    Polynomial.map_C]
  norm_num

/-- `i√3` is a root of `(λ + 1)³ + 8`, checked by direct evaluation:
`(1 + i√3)³ = 1 + 3i√3 - 9 - 3i√3 = -8`. -/
example : ((X + 1) ^ 3 + C (8 : ℂ)).eval ((√3 : ℂ) * Complex.I) = 0 := by
  have h3 : (√3 : ℂ) ^ 2 = 3 := by rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  simp only [eval_add, eval_pow, eval_X, eval_one, eval_C]
  have : ((√3 : ℂ) * Complex.I + 1) ^ 3 =
      ((√3 : ℂ) ^ 2) * (√3 : ℂ) * Complex.I ^ 3 + 3 * (√3 : ℂ) ^ 2 * Complex.I ^ 2 +
        3 * (√3 : ℂ) * Complex.I + 1 := by ring
  rw [this, h3]
  simp only [pow_succ, pow_zero, one_mul, Complex.I_mul_I]
  ring

/-- **Eigenvalues at the Hopf point**: exactly `-3` and `±iω` with `ω = √3`. -/
example (z : ℂ) : (linCharpoly (vectorField 4 (eqRate 4 1)) (fun _ => 1)).IsRoot z ↔
    z = -3 ∨ z = (√3 : ℂ) * Complex.I ∨ z = -((√3 : ℂ) * Complex.I) := by
  rw [linCharpoly_vectorField 4 zero_le_one, show gain 4 1 = 2 by norm_num [gain]]
  exact isRoot_iff_of_gain_eq_two z

/-- `i√3` is a simple eigenvalue at the Hopf point. -/
example : (linCharpoly (vectorField 4 (eqRate 4 1)) (fun _ => 1)).rootMultiplicity
    ((√3 : ℂ) * Complex.I) = 1 := by
  rw [linCharpoly_vectorField 4 zero_le_one, show gain 4 1 = 2 by norm_num [gain]]
  exact rootMultiplicity_eq_one

/-- The eigenvalue curve passes through `i√3` at `μ = 1`. -/
example : hopfEigenvalue 4 1 = (√3 : ℂ) * Complex.I := by
  rw [hopfEigenvalue, show gain 4 1 = 2 by norm_num [gain], rootPlus_two]

/-- Crossing speed at the Hopf point: `a'(1) = 4² · 1 / (1 + 1)² = 4`, so the real part of the
eigenvalue curve has derivative `2`. -/
example : HasDerivAt (hopfEigenvalue 4)
    ((2 : ℝ) + ((√3 / 2 * 4 : ℝ) : ℂ) * Complex.I) 1 := by
  convert hasDerivAt_hopfEigenvalue 4 zero_le_one using 3 <;> norm_num

/-- **Periodic orbits near the Hopf point.** Under the Hopf theorem on `ℝ³`, for every `ε > 0`
there are a rate `α` within `ε` of `2` and a nonconstant periodic solution, with period within
`ε` of `2π/√3`, staying within `ε` of `(1, 1, 1)`. -/
example (hH : HopfBifurcationTheorem 3) :
    ∀ ε > 0, ∃ α T : ℝ, ∃ γ : ℝ → Fin 3 → ℝ, |α - 2| < ε ∧ 0 < T ∧
      |T - 2 * π / √3| < ε ∧ IsIntegralCurve γ (fun _ x => vectorField 4 α x) ∧
      (∀ t, γ (t + T) = γ t) ∧ (∃ t, γ t ≠ γ 0) ∧ ∀ t, dist (γ t) (fun _ => 1) < ε := by
  have h := exists_periodicOrbit hH (n := 4) one_pos (by norm_num [gain])
  rwa [show eqRate 4 1 = 2 by norm_num [eqRate]] at h

/-! ### Below the Hopf point: `n = 4`, `p = 1/2`, `α = 17/32` (stable) -/

/-- `eqRate 4 (1/2) = (1/2)(1 + 1/16) = 17/32`. -/
example : eqRate 4 (1 / 2) = 17 / 32 := by norm_num [eqRate]

/-- The loop gain is `4 · (1/16) / (17/16) = 4/17 < 2`. -/
example : gain 4 (1 / 2) = 4 / 17 := by norm_num [gain]

/-- `-1 - 4/17 = -21/17` is an eigenvalue: `(-21/17 + 1)³ + (4/17)³ = 0`, by direct
evaluation. -/
example : ((X + 1) ^ 3 + C ((4 / 17 : ℝ) ^ 3)).eval (-21 / 17 : ℝ) = 0 := by
  simp only [eval_add, eval_pow, eval_X, eval_one, eval_C]; norm_num

/-- Every eigenvalue at `(1/2, 1/2, 1/2)`, `α = 17/32`, has negative real part. -/
example (z : ℂ) (hz : (linCharpoly (vectorField 4 (eqRate 4 (1 / 2))) (fun _ => 1 / 2)).IsRoot z) :
    z.re < 0 :=
  re_neg_of_isRoot_linCharpoly (by norm_num) (by norm_num [gain]) hz

/-! ### Above the Hopf point: `n = 4`, `p = 2`, `α = 34` (unstable) -/

/-- `eqRate 4 2 = 2 · 17 = 34` and `gain 4 2 = 64/17 > 2`. -/
example : eqRate 4 2 = 34 ∧ gain 4 2 = 64 / 17 := by norm_num [eqRate, gain]

/-- Some eigenvalue at `(2, 2, 2)`, `α = 34`, has positive real part. -/
example : ∃ z, (linCharpoly (vectorField 4 (eqRate 4 2)) (fun _ => 2)).IsRoot z ∧ 0 < z.re :=
  exists_re_pos_of_isRoot_linCharpoly (by norm_num) (by norm_num [gain])

/-! ### No Hopf point: `n = 2` -/

/-- For `n = 2`, `p = 1`: `α = 2` and the loop gain is `2 · 1 / 2 = 1 < 2`. -/
example : eqRate 2 1 = 2 ∧ gain 2 1 = 1 := by norm_num [eqRate, gain]

/-- For `n = 2` the loop gain never reaches `2`: `2p² / (1 + p²) < 2`. -/
example (p : ℝ) (hp : 0 ≤ p) : gain 2 p ≠ 2 := (gain_lt_two_of_le_two le_rfl hp).ne

/-- Direct check that `gain 2 p < 2` from the definition. -/
example (p : ℝ) : gain 2 p < 2 := by
  have : 0 < 1 + p ^ 2 := by positivity
  rw [gain, div_lt_iff₀ this]; push_cast; nlinarith

/-- For `n = 2` the symmetric equilibrium is linearly stable at every level `p ≥ 0`, so no
eigenvalue ever reaches the imaginary axis. -/
example (p : ℝ) (hp : 0 ≤ p) (z : ℂ)
    (hz : (linCharpoly (vectorField 2 (eqRate 2 p)) (fun _ => p)).IsRoot z) : z.re ≠ 0 :=
  (re_neg_of_le_two le_rfl hp hz).ne

/-- The same for the Michaelis–Menten case `n = 1`. -/
example (p : ℝ) (hp : 0 ≤ p) (z : ℂ)
    (hz : (linCharpoly (vectorField 1 (eqRate 1 p)) (fun _ => p)).IsRoot z) : z.re < 0 :=
  re_neg_of_le_two (by norm_num) hp hz

end MathlibExtTest.Biology.Dynamics.Repressilator

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.RepressilatorSixVar
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Tests for the six-variable repressilator: a Hopf point at Hill coefficient `n = 2`
(`β = 1`, equilibrium level `√2`, loop gain `4/3`, frequency `√3/3`), where the protein-only
reduction of T196 has no Hopf point; a stable and an unstable parameter set; and Elowitz and
Leibler's standard regime. Parameter values (equilibria, loop gains, the Hopf condition, the
pure imaginary eigenvalue) are computed from the definitions. -/

open Polynomial Real

namespace MathlibExtTest.Biology.Dynamics.RepressilatorSixVar

open MathlibExt.Biology.Dynamics.RepressilatorSixVar
open MathlibExt.Biology.Dynamics.Repressilator (eqRate gain linCharpoly HopfBifurcationTheorem
  existsUnique_eqLevel)

private lemma sqrt_two_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)

/-! ### The model -/

/-- At the origin the field is `(α, α, α, 0, 0, 0)`: it is not identically zero. -/
example : vectorField 2 6 1 (fun _ => 0) = ![6, 6, 6, 0, 0, 0] := by
  funext k; fin_cases k <;> norm_num [vectorField]

/-- At a non-symmetric state the protein rows are `-β (pᵢ - mᵢ)`: with `m = (1, 0, 0)`,
`p = (0, 0, 0)` and `β = 5`, `ṗ₀ = 5`. -/
example : vectorField 2 6 5 ![1, 0, 0, 0, 0, 0] 3 = 5 := by norm_num [vectorField]

/-- `(1, …, 1)` is an equilibrium for `n = 2`, `α = 2 = eqRate 2 1`, any `β`, from the
definition. -/
example (β : ℝ) : vectorField 2 2 β (fun _ => 1) = 0 := by
  funext k; fin_cases k <;> norm_num [vectorField]

/-- It is the only nonnegative equilibrium for `α = 2`, `β = 1`. -/
example (x : Fin 6 → ℝ) (hx : ∀ j, 0 ≤ x j) (h : vectorField 2 2 1 x = 0) : x = fun _ => 1 :=
  eq_const_of_vectorField_eq_zero (by norm_num) (by norm_num) one_ne_zero zero_le_one
    (by norm_num [eqRate]) hx h

/-- The hypothesis `p ≥ 0` of `eq_const_of_vectorField_eq_zero` is needed: for `n = 1`, `β = 1`,
the negative level `p = -2` gives `α = eqRate 1 (-2) = 2`, and both `(-2, …, -2)` and the
nonnegative state `(1, …, 1)` are equilibria, computed from the definitions. -/
example : eqRate 1 (-2) = 2 ∧ vectorField 1 2 1 (fun _ => -2) = 0 ∧
    vectorField 1 2 1 (fun _ => 1) = 0 := by
  refine ⟨by norm_num [eqRate], ?_, ?_⟩ <;> funext k <;> fin_cases k <;> norm_num [vectorField]

/-- The Jacobian at `(1, …, 1)` (`n = 2`, `α = 2`, `β = 1`, loop gain `1`). -/
example : LinearMap.toMatrix' (fderiv ℝ (vectorField 2 (eqRate 2 1) 1) (fun _ => 1) :
    (Fin 6 → ℝ) →ₗ[ℝ] Fin 6 → ℝ) =
      !![-1, 0, 0, 0, 0, -1; 0, -1, 0, -1, 0, 0; 0, 0, -1, 0, -1, 0;
         1, 0, 0, -1, 0, 0; 0, 1, 0, 0, -1, 0; 0, 0, 1, 0, 0, -1] := by
  rw [toMatrix'_fderiv_vectorField 2 1 zero_le_one, show gain 2 1 = 1 by norm_num [gain]]
  rfl

/-! ### The Hopf point at `n = 2`, `β = 1`: level `√2`, rate `3√2` -/

/-- The critical rate `eqRate 2 √2 = √2 (1 + 2) = 3√2`. -/
example : eqRate 2 √2 = 3 * √2 := by rw [eqRate, sqrt_two_sq]; ring

/-- `(√2, …, √2)` is an equilibrium for `α = 3√2`, `β = 1`, computed from the definition. -/
example : vectorField 2 (3 * √2) 1 (fun _ => √2) = 0 := by
  funext k; fin_cases k <;> simp [vectorField] <;> ring

/-- The loop gain at level `√2`: `2 · 2 / (1 + 2) = 4/3`. -/
lemma gain_two_sqrt_two : gain 2 √2 = 4 / 3 := by
  rw [gain, sqrt_two_sq]; norm_num

/-- The Hopf condition holds: `3 (4/3)² · 1 = 16/3 = (4 - 8/3) (1 + 1)²`. -/
lemma isHopf_two_sqrt_two : IsHopf (gain 2 √2) 1 := by
  rw [gain_two_sqrt_two, IsHopf]; norm_num

/-- The Hopf condition fails at the neighbouring loop gain `1` (`3 ≠ 8`). -/
example : ¬ IsHopf 1 1 := by norm_num [IsHopf]

/-- The Hopf frequency `ω = √3 (4/3) / 4 = √3 / 3`. -/
lemma hopfFreq_two_sqrt_two : hopfFreq (gain 2 √2) 1 = √3 / 3 := by
  rw [gain_two_sqrt_two, hopfFreq]; ring

/-- The characteristic polynomial at the Hopf point is `(λ + 1)⁶ + (4/3)³`. -/
example : (jacobian (4 / 3) 1).charpoly = ((X + 1) * (X + C 1)) ^ 3 + C ((4 / 3 * 1) ^ 3) :=
  charpoly_jacobian _ _

/-- `i √3/3` is a root of `((λ + 1)(λ + 1))³ + (4/3)³`, by direct evaluation:
`(1 + i/√3)² = (2/3)(1 + i√3)` and `(1 + i√3)³ = -8`. -/
example : (((X + 1) * (X + C 1)) ^ 3 + C ((4 / 3 * 1 : ℂ) ^ 3)).eval
    ((√3 / 3 : ℂ) * Complex.I) = 0 := by
  have h3 : (√3 : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have e1 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hw : ((√3 / 3 : ℂ) * Complex.I + 1) * ((√3 / 3 : ℂ) * Complex.I + 1) =
      2 / 3 * (1 + (√3 : ℂ) * Complex.I) := by
    linear_combination (1 / 9 * Complex.I ^ 2) * h3 + (1 / 3) * e1
  have hc : (1 + (√3 : ℂ) * Complex.I) ^ 3 = -8 := by
    linear_combination (3 + (√3 : ℂ) * Complex.I) * (Complex.I ^ 2 * h3 + 3 * e1)
  simp only [eval_add, eval_pow, eval_mul, eval_X, eval_one, eval_C, map_one]
  rw [hw, mul_pow, hc]
  norm_num

/-- **Eigenvalues on the imaginary axis at the Hopf point**: only `±i√3/3`. -/
example (z : ℂ) (hz : (linCharpoly (vectorField 2 (eqRate 2 √2) 1) (fun _ => √2)).IsRoot z)
    (hre : z.re = 0) :
    z = ((√3 / 3 : ℝ) : ℂ) * Complex.I ∨ z = -(((√3 / 3 : ℝ) : ℂ) * Complex.I) := by
  rw [linCharpoly_vectorField 2 1 (by positivity)] at hz
  rw [← hopfFreq_two_sqrt_two]
  exact eq_of_isRoot_of_re_eq_zero (by rw [gain_two_sqrt_two]; norm_num) one_pos hz hre

/-- `i√3/3` is a simple eigenvalue at the Hopf point. -/
example : (linCharpoly (vectorField 2 (eqRate 2 √2) 1) (fun _ => √2)).rootMultiplicity
    (((√3 / 3 : ℝ) : ℂ) * Complex.I) = 1 := by
  rw [linCharpoly_vectorField 2 1 (by positivity), ← hopfFreq_two_sqrt_two]
  exact rootMultiplicity_hopf (by rw [gain_two_sqrt_two]; norm_num) one_pos isHopf_two_sqrt_two

/-- The eigenvalue curve passes through `i√3/3` at the Hopf level `√2`. -/
example : hopfEigenvalue 2 1 √2 = ((√3 / 3 : ℝ) : ℂ) * Complex.I := by
  rw [hopfEigenvalue_hopf one_pos isHopf_two_sqrt_two, hopfFreq_two_sqrt_two]

/-- The real part of the crossing speed is positive. -/
example : HasDerivAt (hopfEigenvalue 2 1) (hopfSpeed 2 1 √2) √2 ∧
    0 < (hopfSpeed 2 1 √2).re :=
  ⟨hasDerivAt_hopfEigenvalue one_pos (by positivity) isHopf_two_sqrt_two,
    re_hopfSpeed_pos (by norm_num) one_pos (by positivity)⟩

/-- **Periodic orbits near the `n = 2` Hopf point.** Under the Hopf theorem on `ℝ⁶`, for every
`ε > 0` there are a rate `α` within `ε` of `3√2` and a nonconstant periodic solution with
`β = 1`, with period within `ε` of `2π / (√3/3)`, staying within `ε` of `(√2, …, √2)`. -/
example (hH : HopfBifurcationTheorem 6) :
    ∀ ε > 0, ∃ α T : ℝ, ∃ γ : ℝ → Fin 6 → ℝ, |α - 3 * √2| < ε ∧ 0 < T ∧
      |T - 2 * π / (√3 / 3)| < ε ∧ IsIntegralCurve γ (fun _ x => vectorField 2 α 1 x) ∧
      (∀ t, γ (t + T) = γ t) ∧ (∃ t, γ t ≠ γ 0) ∧ ∀ t, dist (γ t) (fun _ => √2) < ε := by
  have h := exists_periodicOrbit hH (n := 2) one_pos (by positivity) isHopf_two_sqrt_two
  rwa [show eqRate 2 √2 = 3 * √2 by rw [eqRate, sqrt_two_sq]; ring,
    hopfFreq_two_sqrt_two] at h

/-! ### Inside the boundary: `n = 2`, `β = 1`, level `1` (stable) -/

/-- `eqRate 2 1 = 2` and `gain 2 1 = 2 / 2 = 1`; `3 · 1 · 1 = 3 < (4 - 2) · 4 = 8`. -/
example : eqRate 2 1 = 2 ∧ gain 2 1 = 1 ∧ 3 * (1 : ℝ) ^ 2 * 1 < (4 - 2 * 1) * (1 + 1) ^ 2 := by
  norm_num [eqRate, gain]

/-- `-1 + i` is an eigenvalue (`Q(λ) = (λ + 1)² = -1 = -a β`), with negative real part, by
direct evaluation. -/
example : (((X + 1) * (X + C 1)) ^ 3 + C ((1 * 1 : ℂ) ^ 3)).eval (-1 + Complex.I) = 0 := by
  simp only [eval_add, eval_pow, eval_mul, eval_X, eval_one, eval_C, map_one]
  have : (-1 + Complex.I + 1) * (-1 + Complex.I + 1) = -1 := by ring_nf; exact Complex.I_sq
  rw [this]; norm_num

/-- Every eigenvalue at `(1, …, 1)`, `α = 2`, `β = 1` has negative real part. -/
example (z : ℂ) (hz : (linCharpoly (vectorField 2 (eqRate 2 1) 1) (fun _ => 1)).IsRoot z) :
    z.re < 0 :=
  re_neg_of_isRoot_linCharpoly one_pos zero_le_one (by norm_num [gain]) hz

/-! ### Outside the boundary: `n = 2`, `β = 5`, level `6` (unstable) -/

/-- `eqRate 2 6 = 6 · 37 = 222`, `gain 2 6 = 72/37`, and
`(4 - 144/37) · 36 = 144/37 < 3 (72/37)² · 5`. -/
example : eqRate 2 6 = 222 ∧ gain 2 6 = 72 / 37 ∧
    (4 - 2 * (72 / 37 : ℝ)) * (1 + 5) ^ 2 < 3 * (72 / 37) ^ 2 * 5 := by
  norm_num [eqRate, gain]

/-- Some eigenvalue at `(6, …, 6)`, `α = 222`, `β = 5` has positive real part. -/
example : ∃ z, (linCharpoly (vectorField 2 (eqRate 2 6) 5) (fun _ => 6)).IsRoot z ∧ 0 < z.re :=
  exists_re_pos_of_isRoot_linCharpoly (by norm_num) (by norm_num) (by norm_num [gain])

/-! ### Elowitz–Leibler's standard regime: `n = 2`, `α = 216`, `β = 5` -/

/-- The equilibrium level for `α = 216` exists (T196) and lies above `5`
(`5 (1 + 25) = 130 < 216`). -/
example : ∃ p : ℝ, 0 < p ∧ eqRate 2 p = 216 ∧ 5 < p := by
  obtain ⟨p, ⟨hp, hpα⟩, -⟩ := existsUnique_eqLevel 2 (α := 216) (by norm_num)
  refine ⟨p, hp, hpα, ?_⟩
  by_contra h
  have h := not_lt.1 h
  unfold eqRate at hpα
  nlinarith [sq_nonneg p]

/-- **The standard regime is unstable**: some eigenvalue at the symmetric equilibrium has
positive real part. -/
example : ∃ p : ℝ, 0 < p ∧ eqRate 2 p = 216 ∧
    ∃ z, (linCharpoly (vectorField 2 216 5) (fun _ => p)).IsRoot z ∧ 0 < z.re := by
  obtain ⟨p, ⟨hp, hpα⟩, -⟩ := existsUnique_eqLevel 2 (α := 216) (by norm_num)
  exact ⟨p, hp, hpα, exists_re_pos_standardRegime hp hpα⟩

end MathlibExtTest.Biology.Dynamics.RepressilatorSixVar

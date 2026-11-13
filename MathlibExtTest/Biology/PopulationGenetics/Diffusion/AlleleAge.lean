/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.PopulationGenetics.Diffusion.AlleleAge

/-! Tests for the allele-age densities: neutral values, the closed forms at concrete
frequencies, the boundary and junk values of the total definitions, the symmetry, the paper's
units, and the Maruyama effect at `x = 1/2`. -/

open Real Set

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.AlleleAge

open MathlibExt.Biology.PopulationGenetics.Diffusion

/-- Neutral reduction: `Ψ(1/2, 1/4) = G(1/2, 1/4) = 4/3`. -/
example : selectionGreen 0 (1 / 2) (1 / 4) = 4 / 3 := by
  rw [selectionGreen_zero ⟨by norm_num, by norm_num⟩]
  norm_num [neutralGreen]

/-- The general Green kernel at genic selection is the sojourn density (here `σ = 1`). -/
example : greenFunction (fun x => 1 * x * (1 - x)) (fun x => x * (1 - x)) (1 / 2) (1 / 4) =
    selectionGreen 1 (1 / 2) (1 / 4) :=
  greenFunction_eq_selectionGreen 1 (by norm_num) (by norm_num)

/-- The sojourn density with selection is positive in the interior (here `σ = 1`). -/
example : 0 < selectionGreen 1 (1 / 2) (1 / 4) := by
  unfold selectionGreen
  have h1 := kimuraFixation_pos 1 (by norm_num : (0 : ℝ) < 1 / 4)
  have h2 := kimuraFixation_lt_one 1 (by norm_num : (1 / 2 : ℝ) < 1)
  have h3 := kimuraSlope_pos 1
  rw [min_eq_right (by norm_num), max_eq_left (by norm_num)]
  have : 0 < 1 - kimuraFixation 1 (1 / 2) := by linarith
  positivity

/-- Junk value outside the domain: at `x = 0` the denominator vanishes and Lean returns `0`. -/
example (σ p : ℝ) : selectionGreen σ p 0 = 0 := by simp [selectionGreen]

/-- Boundary values of the Green integral, with selection. -/
example (σ : ℝ) (g : ℝ → ℝ) : ∫ x in (0 : ℝ)..1, selectionGreen σ 0 x * g x = 0 :=
  integral_selectionGreen_left σ g

example (σ : ℝ) (g : ℝ → ℝ) : ∫ x in (0 : ℝ)..1, selectionGreen σ 1 x * g x = 0 :=
  integral_selectionGreen_right σ g

/-- Off the diagonal `Ψ(·, x)` is annihilated by the generator (deleterious case `σ = -3`). -/
example : generator (-3) (fun q => selectionGreen (-3) q (1 / 2)) (1 / 4) = 0 :=
  generator_selectionGreen_of_lt (-3) (by norm_num)

/-- The jump of `∂_p Ψ(p, x)` at `p = x` is `-2 / (x (1 - x))`. -/
example (σ x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    -(2 * kimuraFixation σ x / (x * (1 - x))) - 2 * (1 - kimuraFixation σ x) / (x * (1 - x)) =
      -2 / (x * (1 - x)) := by
  have := hasDerivWithinAt_selectionGreen_Iic σ hx
  have := hasDerivWithinAt_selectionGreen_Ici σ hx
  ring

/-- Neutral densities: `Ψ₁ = 2` and `Ψ₂(1/2, 3/4) = 2 (1/2) (1/4) / ((1/2) (3/4)) = 2/3`. -/
example (z : ℝ) : maruyamaBelow 0 z = 2 := by simp [maruyamaBelow]

example : maruyamaAbove 0 (1 / 2) (3 / 4) = 2 / 3 := by norm_num [maruyamaAbove]

/-- The conditional sojourn density between `p = 1/4` and `x = 3/4` is the closed form `Ψ₁`. -/
example (σ : ℝ) : ageDensity σ (1 / 4) (3 / 4) (1 / 2) = maruyamaBelow σ (1 / 2) :=
  ageDensity_of_le_of_le σ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Above the current frequency it is `Ψ₂`; the boundary case `z = x` is allowed. -/
example (σ : ℝ) : ageDensity σ (1 / 4) (1 / 2) (1 / 2) = maruyamaAbove σ (1 / 2) (1 / 2) :=
  ageDensity_of_le_of_ge σ (by norm_num) (by norm_num) le_rfl (by norm_num)

/-- Junk value outside the domain: for `σ ≠ 0`, the closed form `Ψ₁` returns `0` at `z = 0`
(where its continuous extension is positive). -/
example (σ : ℝ) (hσ : σ ≠ 0) : maruyamaBelow σ 0 = 0 := by simp [maruyamaBelow, hσ]

/-- At `z = 1` the closed form `Ψ₂` vanishes. -/
example (σ x : ℝ) : maruyamaAbove σ x 1 = 0 := maruyamaAbove_one_right σ x

/-- Neutral mean age at `x = 1/2`: `-2 (1/2) log (1/2) / (1/2) = 2 log 2` (units of `2N`
generations). -/
example : meanAge 0 (1 / 2) = 2 * log 2 := by
  rw [meanAge_zero ⟨by norm_num, by norm_num⟩, one_div, log_inv]
  ring

/-- Advantageous and deleterious alleles of the same strength have the same mean age. -/
example : meanAge (-1) (1 / 2) = meanAge 1 (1 / 2) := meanAge_neg 1 ⟨by norm_num, by norm_num⟩

/-- **Maruyama effect** at `x = 1/2`, `σ = -1` (deleterious): younger than `2 log 2`. -/
example : meanAge (-1) (1 / 2) < 2 * log 2 := by
  have h := meanAge_lt (σ := -1) (x := 1 / 2) (by norm_num) ⟨by norm_num, by norm_num⟩
  rw [meanAge_zero ⟨by norm_num, by norm_num⟩] at h
  have e : -2 * (1 / 2 : ℝ) * log (1 / 2) / (1 - 1 / 2) = 2 * log 2 := by
    rw [one_div, log_inv]; ring
  linarith

/-- Paper units: with `N = 10⁴` diploids and `s = -10⁻³` (so `γ = 4Ns = -40`), the paper's
`Ψ₁` in generations is `2N` times the density in units of `2N` generations. -/
example (z : ℝ) :
    2 * 10 ^ 4 * maruyamaBelow (2 * 10 ^ 4 * (-10⁻¹ ^ 3)) z =
      (exp (-(4 * 10 ^ 4 * (-10⁻¹ ^ 3)) * (1 - z)) - 1) *
          (exp (-(4 * 10 ^ 4 * (-10⁻¹ ^ 3)) * z) - 1) /
        (-10⁻¹ ^ 3 * z * (1 - z) * (1 - exp (-(4 * 10 ^ 4 * (-10⁻¹ ^ 3))))) :=
  maruyamaBelow_generations (by norm_num) (by norm_num) z

/-- Green's representation with selection, `g = 1`: the mean absorption time
`v(p) = ∫₀¹ Ψ(p, x) dx` solves `L_σ v = -1` (here `σ = 2`, `p = 1/3`). -/
example : generator 2 (fun q => ∫ x in (0 : ℝ)..1, selectionGreen 2 q x * 1) (1 / 3) = -1 :=
  generator_integral_selectionGreen 2 (g := fun _ => 1) continuous_const ⟨by norm_num, by norm_num⟩

/-- Stronger selection, younger alleles: `σ = 2` versus `σ = -1` at `x = 1/2`. -/
example : meanAge 2 (1 / 2) < meanAge (-1) (1 / 2) :=
  meanAge_lt_meanAge_of_abs_lt ⟨by norm_num, by norm_num⟩ (by norm_num [abs_of_pos])

/-- The mean age is the limit of total conditional sojourn times as `p → 0⁺`. -/
example (σ : ℝ) :
    Filter.Tendsto (fun p => ∫ z in (0 : ℝ)..1, ageDensity σ p (1 / 2) z)
      (nhdsWithin 0 (Ioi 0)) (nhds (meanAge σ (1 / 2))) :=
  tendsto_integral_ageDensity σ ⟨by norm_num, by norm_num⟩

open MeasureTheory in
/-- Non-vacuity of the Chapman–Kolmogorov hypothesis: `w(p, x, t) = e^{-t}` (uniform in the
target frequency, killed at rate `1`) satisfies it, and the identity then reads
`∫₀^∞ t e^{-t} dt = ∫₀¹ 1 · 1 dy`. -/
example (p x : ℝ) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal t * ENNReal.ofReal (exp (-t)) =
      ∫⁻ _ in Ioo (0 : ℝ) 1, (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (exp (-s))) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (exp (-t)) := by
  refine lintegral_mul_eq_lintegral_sojourn_mul (fun _ _ t => ENNReal.ofReal (exp (-t)))
    (by fun_prop) (fun _ _ s t _ _ => ?_) p x
  rw [setLIntegral_const, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one,
    ← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add, neg_add]

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.AlleleAge

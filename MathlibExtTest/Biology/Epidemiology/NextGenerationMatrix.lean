/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Epidemiology.NextGenerationMatrix

/-! Tests for the next-generation matrix: for an SIS/SIR-type model with one infected
compartment, `F = (β)` and `V = (γ)` (transmission rate `β ≥ 0`, removal rate `γ > 0`),
`R₀ = ρ(F V⁻¹) = β / γ`; the hypotheses of the threshold theorems are satisfiable
(non-vacuity witness), and the threshold reads `β - γ < 0 ↔ β / γ < 1`. -/

open Matrix

namespace MathlibExtTest.Biology.Epidemiology.NextGenerationMatrix

open MathlibExt.Biology.Epidemiology.NextGenerationMatrix

/-- The complexification of the real `1 × 1` scalar matrix `c • 1` is the complex scalar. -/
example (c : ℝ) :
    (c • (1 : Matrix (Fin 1) (Fin 1) ℝ)).map (algebraMap ℝ ℂ) =
      algebraMap ℂ (Matrix (Fin 1) (Fin 1) ℂ) (c : ℂ) :=
  Matrix.map_smul_one_algebraMap c

example (c : ℝ) :
    spectrum ℂ ((c • (1 : Matrix (Fin 1) (Fin 1) ℝ)).map (algebraMap ℝ ℂ)) = {(c : ℂ)} :=
  Matrix.spectrum_smul_one c

/-- **Non-vacuity witness.** The removal rate `γ > 0` gives a nonsingular M-matrix
`V = (γ)`. -/
example {γ : ℝ} (hγ : 0 < γ) :
    (γ • (1 : Matrix (Fin 1) (Fin 1) ℝ)).IsNonsingularMMatrix :=
  isNonsingularMMatrix_smul_one hγ

/-- **`R₀ = β / γ`** for one infected compartment. -/
example (β : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    R0 (β • (1 : Matrix (Fin 1) (Fin 1) ℝ)) (γ • 1) = |β / γ| :=
  R0_smul_one β hγ

/-- For `β ≥ 0`, `R₀ = β / γ`. -/
example {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ) :
    R0 (β • (1 : Matrix (Fin 1) (Fin 1) ℝ)) (γ • 1) = β / γ :=
  R0_smul_one_of_nonneg hβ hγ

/-- `F = (β)` is entrywise nonnegative for `β ≥ 0`. -/
example {β : ℝ} (hβ : 0 ≤ β) (i j : Fin 1) :
    0 ≤ (β • (1 : Matrix (Fin 1) (Fin 1) ℝ)) i j :=
  smul_one_nonneg hβ i j

/-- **The threshold for one infected compartment**: `F - V = (β - γ)` is Hurwitz iff
`β / γ < 1`. -/
example {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ) :
    (β • (1 : Matrix (Fin 1) (Fin 1) ℝ) - γ • 1).IsHurwitz ↔ β / γ < 1 := by
  rw [isHurwitz_sub_iff_R0_lt_one (smul_one_nonneg hβ) (isNonsingularMMatrix_smul_one hγ),
    R0_smul_one_of_nonneg hβ hγ]

/-- With `β = 3`, `γ = 1` (`R₀ = 3 > 1`), the linearization has an unstable eigenvalue. -/
example : ∃ μ ∈ spectrum ℂ (((3 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) - (1 : ℝ) • 1).map
    (algebraMap ℝ ℂ)), 0 < μ.re :=
  (exists_re_pos_iff_one_lt_R0 (smul_one_nonneg (by norm_num))
    (isNonsingularMMatrix_smul_one one_pos)).2 (by rw [R0_smul_one_of_nonneg] <;> norm_num)

/-- **Disease-free equilibrium, stability half, conditional decay form.** For the model
`x' = (β - γ) x` with one infected compartment and no other compartment (`κ = Fin 0`),
`β = 1/2`, `γ = 1` (`R₀ = 1/2`), every global solution starting near the equilibrium `0`
decays exponentially. -/
example (f : (Fin 1 ⊕ Fin 0 → ℝ) → Fin 1 ⊕ Fin 0 → ℝ) (hf : f 0 = 0)
    (hfJ : HasFDerivAt f (LinearMap.toContinuousLinearMap (Matrix.toLin'
      (fromBlocks ((1 / 2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) - (1 : ℝ) • 1) 0
        (0 : Matrix (Fin 0) (Fin 1) ℝ) (0 : Matrix (Fin 0) (Fin 0) ℝ)))) 0) :
    ∃ δ K α : ℝ, 0 < δ ∧ 0 < K ∧ 0 < α ∧ ∀ x : ℝ → Fin 1 ⊕ Fin 0 → ℝ,
      (∀ t, 0 ≤ t → HasDerivAt x (f (x t)) t) → ‖x 0 - 0‖ < δ →
        ∀ t, 0 ≤ t → ‖x t - 0‖ ≤ K * Real.exp (-(α * t)) * ‖x 0 - 0‖ :=
  globalSolution_decay_of_R0_lt_one hf hfJ (smul_one_nonneg (by norm_num))
    (isNonsingularMMatrix_smul_one one_pos) (fun μ hμ => by simp [spectrum.of_subsingleton] at hμ)
    (by rw [R0_smul_one_of_nonneg] <;> norm_num)

end MathlibExtTest.Biology.Epidemiology.NextGenerationMatrix

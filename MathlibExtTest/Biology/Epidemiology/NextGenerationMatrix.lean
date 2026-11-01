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
theorem map_smul_one (c : ℝ) :
    (c • (1 : Matrix (Fin 1) (Fin 1) ℝ)).map (algebraMap ℝ ℂ) =
      algebraMap ℂ (Matrix (Fin 1) (Fin 1) ℂ) (c : ℂ) := by
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.algebraMap_matrix_apply]

theorem spectrum_smul_one (c : ℝ) :
    spectrum ℂ ((c • (1 : Matrix (Fin 1) (Fin 1) ℝ)).map (algebraMap ℝ ℂ)) = {(c : ℂ)} := by
  rw [map_smul_one, spectrum.scalar_eq]

/-- **Non-vacuity witness.** The removal rate `γ > 0` gives a nonsingular M-matrix
`V = (γ)`. -/
theorem isNonsingularMMatrix_smul_one {γ : ℝ} (hγ : 0 < γ) :
    (γ • (1 : Matrix (Fin 1) (Fin 1) ℝ)).IsNonsingularMMatrix := by
  refine ⟨fun i j hij => absurd (Subsingleton.elim i j) hij, ?_⟩
  intro μ hμ
  rw [← neg_smul, spectrum_smul_one, Set.mem_singleton_iff] at hμ
  simp [hμ, hγ]

/-- **`R₀ = β / γ`** for one infected compartment. -/
theorem R0_smul_one (β : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    R0 (β • (1 : Matrix (Fin 1) (Fin 1) ℝ)) (γ • 1) = |β / γ| := by
  have hinv : (γ • (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹ = γ⁻¹ • 1 := by
    refine Matrix.inv_eq_left_inv ?_
    rw [smul_mul_smul, mul_one, inv_mul_cancel₀ hγ.ne', one_smul]
  have hK : β • (1 : Matrix (Fin 1) (Fin 1) ℝ) * (γ • 1)⁻¹ = (β / γ) • 1 := by
    rw [hinv, smul_mul_smul, mul_one, div_eq_mul_inv]
  rw [R0, hK, spectralRadius, quasispectrum_eq_spectrum_union_zero, spectrum_smul_one]
  rw [Set.union_singleton, iSup_insert, iSup_singleton]
  simp [abs_div]

/-- For `β ≥ 0`, `R₀ = β / γ`. -/
theorem R0_smul_one_of_nonneg {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ) :
    R0 (β • (1 : Matrix (Fin 1) (Fin 1) ℝ)) (γ • 1) = β / γ := by
  rw [R0_smul_one β hγ, abs_of_nonneg (div_nonneg hβ hγ.le)]

/-- `F = (β)` is entrywise nonnegative for `β ≥ 0`. -/
theorem smul_one_nonneg {β : ℝ} (hβ : 0 ≤ β) (i j : Fin 1) :
    0 ≤ (β • (1 : Matrix (Fin 1) (Fin 1) ℝ)) i j := by
  fin_cases i; fin_cases j; simpa using hβ

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

/-- **Disease-free equilibrium, stability half.** For the model `x' = (β - γ) x` with one
infected compartment and no other compartment (`κ = Fin 0`), `β = 1/2`, `γ = 1`
(`R₀ = 1/2`), the equilibrium `0` is locally exponentially stable. -/
example (f : (Fin 1 ⊕ Fin 0 → ℝ) → Fin 1 ⊕ Fin 0 → ℝ) (hf : f 0 = 0)
    (hfJ : HasFDerivAt f (LinearMap.toContinuousLinearMap (Matrix.toLin'
      (fromBlocks ((1 / 2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) - (1 : ℝ) • 1) 0
        (0 : Matrix (Fin 0) (Fin 1) ℝ) (0 : Matrix (Fin 0) (Fin 0) ℝ)))) 0) :
    ∃ δ K α : ℝ, 0 < δ ∧ 0 < K ∧ 0 < α ∧ ∀ x : ℝ → Fin 1 ⊕ Fin 0 → ℝ,
      (∀ t, 0 ≤ t → HasDerivAt x (f (x t)) t) → ‖x 0 - 0‖ < δ →
        ∀ t, 0 ≤ t → ‖x t - 0‖ ≤ K * Real.exp (-(α * t)) * ‖x 0 - 0‖ :=
  exists_locallyExponentiallyStable_of_R0_lt_one hf hfJ (smul_one_nonneg (by norm_num))
    (isNonsingularMMatrix_smul_one one_pos) (fun μ hμ => by simp [spectrum.of_subsingleton] at hμ)
    (by rw [R0_smul_one_of_nonneg] <;> norm_num)

end MathlibExtTest.Biology.Epidemiology.NextGenerationMatrix

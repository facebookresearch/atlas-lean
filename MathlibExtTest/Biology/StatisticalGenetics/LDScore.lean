/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.LDScore

@[expose] public section

open MeasureTheory MathlibExt.Biology.StatisticalGenetics.LDScore
open scoped ENNReal

namespace MathlibExtTest.Biology.StatisticalGenetics.LDScore

/-! ### LD scores of concrete genotype matrices -/

/-- Two individuals, two markers in perfect LD (identical standardized columns `(1, -1)`). -/
def X2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; -1, -1]

example : ldCorr X2 0 1 = 1 := by
  simp [ldCorr, X2, Fin.sum_univ_two]

/-- Perfect LD with one other marker: `ℓ = r₀₀² + r₀₁² = 2`. -/
example : ldScore X2 0 = 2 := by
  simp [ldScore, ldCorr, X2, Fin.sum_univ_two]
  norm_num

/-- Two individuals, two markers in linkage equilibrium (orthogonal columns): `ℓ = 1`. -/
def X2' : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, -1]

example : ldScore X2' 1 = 1 := by
  simp [ldScore, ldCorr, X2', Fin.sum_univ_two]

/-! ### A non-vacuous model

`Ω = Fin 4` with the uniform probability measure and the four orthogonal Hadamard sign vectors
scaled by `1/2` (second moment `1/4` each): three markers with effects `h₁/2, h₂/2, h₃/2`
(`h² / M = (3/4) / 3 = 1/4`) and one individual with noise `h₀/2` (`1 - h² = 1/4`). -/

/-- The uniform probability measure on `Fin 4`. -/
noncomputable def μ4 : Measure (Fin 4) := (4⁻¹ : ℝ≥0∞) • Measure.count

instance : IsProbabilityMeasure μ4 :=
  ⟨by simpa [μ4] using ENNReal.inv_mul_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)⟩

/-- Integration against `μ4` is averaging over the four outcomes. -/
theorem integral_μ4 (f : Fin 4 → ℝ) : ∫ ω, f ω ∂μ4 = (f 0 + f 1 + f 2 + f 3) / 4 := by
  simp only [μ4, integral_smul_measure, integral_count, Fin.sum_univ_four]
  norm_num
  ring

/-- Hadamard sign vectors of length `4`, scaled by `1/2`. -/
noncomputable def had : Fin 4 → Fin 4 → ℝ :=
  ![![1/2, 1/2, 1/2, 1/2], ![1/2, 1/2, -1/2, -1/2], ![1/2, -1/2, 1/2, -1/2],
    ![1/2, -1/2, -1/2, 1/2]]

/-- The witness model: `N = 1`, `M = 3`, `h² = 3/4`. -/
noncomputable def D : Model μ4 1 3 where
  h2 := 3 / 4
  beta := fun k => had k.succ
  eps := fun _ => had 0
  memLp_beta := fun _ => MemLp.of_discrete
  memLp_eps := fun _ => MemLp.of_discrete
  integral_beta_mul := by
    intro k l
    fin_cases k <;> fin_cases l <;> simp [integral_μ4, had] <;> norm_num
  integral_eps_mul := by
    intro i i'
    simp [Subsingleton.elim i i', integral_μ4, had]
    norm_num
  integral_beta_mul_eps := by
    intro k i
    fin_cases k <;> fin_cases i <;> simp [integral_μ4, had] <;> norm_num

/-- A `1 × 3` genotype matrix whose columns have sum of squares `N = 1`. -/
def X13 : Matrix (Fin 1) (Fin 3) ℝ := !![1, -1, 1]

/-- All three markers are in perfect LD: `ℓ 0 = 3`. -/
theorem ldScore_X13 : ldScore X13 0 = 3 := by
  simp [ldScore, ldCorr, X13, Fin.sum_univ_three]
  norm_num

/-- The LD-score identity on the witness: `𝔼[χ²] = 1 * (3/4) / 3 * 3 + (1 - 3/4) = 1`. -/
example : ∫ ω, D.chiSq X13 0 ω ∂μ4 = 1 := by
  rw [D.integral_chiSq_of_standardized X13 one_ne_zero 0 (by simp [X13]), ldScore_X13]
  norm_num [D]

/-- The same value by direct computation of the expectation. -/
example : ∫ ω, D.chiSq X13 0 ω ∂μ4 = 1 := by
  simp [integral_μ4, Model.chiSq, Model.betaHat, Model.pheno, D, X13, had,
    Fin.sum_univ_three]
  norm_num

/-- The general form without standardization: scaling the whole genotype matrix by `2`
multiplies the sum of squares of column `0` by `4` (from `1` to `4`), so the noise term is
`(1 - h²) * 4 / N`. -/
example : ∫ ω, D.chiSq (2 • X13) 0 ω ∂μ4 =
    1 * (3 / 4) / 3 * ldScore (2 • X13) 0 + (1 - 3 / 4) * 4 / 1 := by
  rw [D.integral_chiSq]
  simp [D, X13]
  norm_num

/-- The heritability of the witness lies in `[0, 1]`, as forced by the model. -/
example : 0 ≤ D.h2 ∧ D.h2 ≤ 1 := ⟨D.h2_nonneg (by norm_num), D.h2_le_one (by norm_num)⟩

/-- Boundary (junk value outside the domain): with no individuals the statistic is `0` by the
convention `x / 0 = 0`, and the general identity degenerates to `0 = 0`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {M : ℕ} (D' : Model μ 0 M)
    (X : Matrix (Fin 0) (Fin M) ℝ) (j : Fin M) (ω : Ω) : D'.chiSq X j ω = 0 := by
  simp [Model.chiSq]

end MathlibExtTest.Biology.StatisticalGenetics.LDScore

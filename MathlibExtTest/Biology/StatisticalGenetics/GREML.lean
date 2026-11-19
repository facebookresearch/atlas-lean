/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.GREML

@[expose] public section

open MeasureTheory Filter Topology MathlibExt.Biology.StatisticalGenetics
open MathlibExt.Biology.StatisticalGenetics.GREML
open scoped ENNReal

namespace MathlibExtTest.Biology.StatisticalGenetics.GREML

/-! ### The GRM, the pairs and the estimator on concrete data -/

/-- Two individuals, two standardized markers with columns `(1, -1)`. -/
def X2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; -1, -1]

/-- Two individuals whose GRM entry vanishes: columns `(1, -1)` and `(1, 1)`. -/
def X0 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; -1, 1]

example : grm X2 0 1 = -1 := by
  simp [grm, X2, Fin.sum_univ_two]

example : grm X2 0 0 = 1 := by
  simp [grm, X2, Fin.sum_univ_two]

example : grm X0 0 1 = 0 := by
  simp [grm, X0, Fin.sum_univ_two]

/-- With two individuals there is exactly one pair. -/
theorem pairs_two : pairs 2 = {(0, 1)} := by decide

/-- With three individuals there are three pairs. -/
example : (pairs 3).card = 3 := by decide

/-- `ĥ² = A₀₁ y₀ y₁ / A₀₁² = (-1) * 6 / 1 = -6`. -/
example : heEstimate (grm X2) ![2, 3] = -6 := by
  simp [heEstimate, pairs_two, grm, X2, Fin.sum_univ_two]; norm_num

/-- Boundary: when every off-diagonal GRM entry vanishes the estimator is `0` (`x / 0 = 0`). -/
example (y : Fin 2 → ℝ) : heEstimate (grm X0) y = 0 := by
  simp [heEstimate, pairs_two, grm, X0, Fin.sum_univ_two]

/-- Three individuals, `A = !![_, 1, 2; _, _, 3; _, _, _]`, `y = (1, 1, 1)`:
`ĥ² = (1 + 2 + 3) / (1 + 4 + 9) = 3 / 7`. -/
example : heEstimate !![0, 1, 2; 1, 0, 3; 2, 3, 0] ![1, 1, 1] = 3 / 7 := by
  have h : pairs 3 = {(0, 1), (0, 2), (1, 2)} := by decide
  simp [heEstimate, h]; norm_num

/-- The residual sum of squares at the estimate (`0`, the cross-product is fitted exactly
with one pair) is below that at slope `0` (`36`). -/
example : heRSS (grm X2) ![2, 3] (heEstimate (grm X2) ![2, 3]) = 0 ∧
    heRSS (grm X2) ![2, 3] 0 = 36 := by
  simp [heRSS, heEstimate, pairs_two, grm, X2, Fin.sum_univ_two]; norm_num

/-! ### A non-vacuous model

`Ω = Fin 4` with the uniform probability measure and the four orthogonal Hadamard sign vectors
`h₀, …, h₃` (second moment `1` each). Two markers with effects `(2/3) h₀, (2/3) h₁`
(`h² / M = (8/9) / 2 = 4/9`) and two individuals with noise `(1/3) h₂, (1/3) h₃`
(`1 - h² = 1/9`). -/

/-- The uniform probability measure on `Fin 4`. -/
noncomputable def μ4 : Measure (Fin 4) := (4⁻¹ : ℝ≥0∞) • Measure.count

instance : IsProbabilityMeasure μ4 :=
  ⟨by simpa [μ4] using ENNReal.inv_mul_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)⟩

theorem integral_μ4 (f : Fin 4 → ℝ) : ∫ ω, f ω ∂μ4 = (f 0 + f 1 + f 2 + f 3) / 4 := by
  simp only [μ4, integral_smul_measure, integral_count, Fin.sum_univ_four]
  norm_num
  ring

/-- Hadamard sign vectors of length `4`. -/
def had : Fin 4 → Fin 4 → ℝ :=
  ![![1, 1, 1, 1], ![1, 1, -1, -1], ![1, -1, 1, -1], ![1, -1, -1, 1]]

/-- The witness model: `N = 2`, `M = 2`, `h² = 8/9`. -/
noncomputable def D : LDScore.Model μ4 2 2 where
  h2 := 8 / 9
  beta := fun k ω => 2 / 3 * had (Fin.castAdd 2 k) ω
  eps := fun i ω => 1 / 3 * had (Fin.natAdd 2 i) ω
  memLp_beta := fun _ => MemLp.of_discrete
  memLp_eps := fun _ => MemLp.of_discrete
  integral_beta_mul := by
    intro k l
    fin_cases k <;> fin_cases l <;> simp [integral_μ4, had] <;> norm_num
  integral_eps_mul := by
    intro i i'
    fin_cases i <;> fin_cases i' <;> simp [integral_μ4, had] <;> norm_num
  integral_beta_mul_eps := by
    intro k i
    fin_cases k <;> fin_cases i <;> simp [integral_μ4, had]

/-- The HE identity on the witness, computed directly: `𝔼[y₀ y₁] = -8/9 = h² A₀₁`. -/
example : ∫ ω, D.pheno X2 0 ω * D.pheno X2 1 ω ∂μ4 = -8 / 9 := by
  simp [integral_μ4, LDScore.Model.pheno, D, X2, had, Fin.sum_univ_two]; norm_num

/-- The same value through `integral_pheno_mul_pheno_of_ne`. -/
example : ∫ ω, D.pheno X2 0 ω * D.pheno X2 1 ω ∂μ4 = -8 / 9 := by
  rw [integral_pheno_mul_pheno_of_ne D X2 (by decide)]
  simp [D, grm, X2, Fin.sum_univ_two]; norm_num

/-- The diagonal: `𝔼[y₀²] = h² A₀₀ + 1 - h² = 8/9 + 1/9 = 1`, computed directly. -/
example : ∫ ω, D.pheno X2 0 ω * D.pheno X2 0 ω ∂μ4 = 1 := by
  simp [integral_μ4, LDScore.Model.pheno, D, X2, had, Fin.sum_univ_two]; norm_num

/-- Unbiasedness on the witness, computed directly: `𝔼[ĥ²] = 8/9 = h²`. -/
example : ∫ ω, heEstimate (grm X2) (fun i => D.pheno X2 i ω) ∂μ4 = 8 / 9 := by
  simp [integral_μ4, heEstimate, pairs_two, grm, LDScore.Model.pheno, D, X2, had,
    Fin.sum_univ_two]
  norm_num

/-- The same value through `integral_heEstimate`. -/
example : ∫ ω, heEstimate (grm X2) (fun i => D.pheno X2 i ω) ∂μ4 = 8 / 9 := by
  rw [integral_heEstimate D X2 (by simp [pairs_two, grm, X2, Fin.sum_univ_two])]
  rfl

/-- Boundary: when `∑_{i<j} A_ij² = 0` the estimator is identically `0`, so it is biased,
`𝔼[ĥ²] = 0 ≠ 8/9 = h²`; the hypothesis of `integral_heEstimate` is needed. -/
example : ∫ ω, heEstimate (grm X0) (fun i => D.pheno X0 i ω) ∂μ4 = 0 ∧ D.h2 ≠ 0 := by
  refine ⟨?_, by norm_num [D]⟩
  simp [heEstimate, pairs_two, grm, X0, Fin.sum_univ_two]

/-- The mean-squared error on the witness, computed directly: the deviations
`y₀ y₁ + 8/9` are `∓7/9`, so `𝔼[(ĥ² - h²)²] = 49/81`. -/
example : ∫ ω, (heEstimate (grm X2) (fun i => D.pheno X2 i ω) - D.h2) ^ 2 ∂μ4 = 49 / 81 := by
  simp [integral_μ4, heEstimate, pairs_two, grm, LDScore.Model.pheno, D, X2, had,
    Fin.sum_univ_two]
  norm_num

/-- `integral_heEstimate_sub_sq_le` on the witness with the row-sum constant `C = 49/81`
(one pair, `∫ heDev² = 49/81`): the bound `C / ∑ A_ij² = 49/81` is attained. -/
example : ∫ ω, (heEstimate (grm X2) (fun i => D.pheno X2 i ω) - D.h2) ^ 2 ∂μ4 ≤ 49 / 81 := by
  have hS : ∑ p ∈ pairs 2, grm X2 p.1 p.2 ^ 2 = 1 := by
    simp [pairs_two, grm, X2, Fin.sum_univ_two]
  have h := integral_heEstimate_sub_sq_le D X2 (by rw [hS]; norm_num)
    (fun _ _ => MemLp.of_discrete) (C := 49 / 81) (by
      intro p hp
      rw [pairs_two, Finset.mem_singleton] at hp
      subst hp
      simp [pairs_two, heDev, integral_μ4, grm, LDScore.Model.pheno, D, X2, had,
        Fin.sum_univ_two]
      norm_num)
  rwa [hS, div_one] at h

/-! ### Non-vacuity of the consistency hypotheses

A deterministic sequence of models on `Unit`: `n + 1` individuals, one marker with genotype `1`
for everyone and effect `β = 1`, no noise, `h² = 1`. Every cross-product equals `h² A_ij = 1`,
so the covariance row sums vanish (`C = 0`), and `∑_{i<j} A_ij² = n (n + 1) / 2 → ∞`. -/

/-- The model with `n + 1` individuals. -/
noncomputable def Dn (n : ℕ) : LDScore.Model (Measure.dirac ()) (n + 1) 1 where
  h2 := 1
  beta := fun _ _ => 1
  eps := fun _ _ => 0
  memLp_beta := fun _ => MemLp.of_discrete
  memLp_eps := fun _ => MemLp.of_discrete
  integral_beta_mul := by intro k l; simp [Subsingleton.elim k l]
  integral_eps_mul := by intro i i'; split_ifs <;> simp
  integral_beta_mul_eps := by intro k i; simp

/-- Everyone has genotype `1` at the single marker. -/
def Xn (n : ℕ) : Matrix (Fin (n + 1)) (Fin 1) ℝ := fun _ _ => 1

theorem grm_Xn (n : ℕ) (i j : Fin (n + 1)) : grm (Xn n) i j = 1 := by
  simp [grm, Xn]

theorem heDev_Dn (n : ℕ) (p : Fin (n + 1) × Fin (n + 1)) (ω : Unit) :
    heDev (Dn n) (Xn n) p ω = 0 := by
  simp [heDev, grm_Xn, LDScore.Model.pheno, Dn, Xn]

/-- The off-diagonal GRM energy is at least `n`: the pairs `(0, j + 1)` alone contribute `n`. -/
theorem le_sum_grm_Xn (n : ℕ) : (n : ℝ) ≤ ∑ p ∈ pairs (n + 1), grm (Xn n) p.1 p.2 ^ 2 := by
  simp only [grm_Xn, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsub : (Finset.univ.map ⟨fun j : Fin n => ((0 : Fin (n + 1)), j.succ),
      fun a b h => Fin.succ_injective _ (Prod.ext_iff.1 h).2⟩) ⊆ pairs (n + 1) := by
    intro p hp
    simp only [Finset.mem_map, Finset.mem_univ, true_and] at hp
    obtain ⟨j, rfl⟩ := hp
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.succ_pos j⟩
  have := Finset.card_le_card hsub
  simp only [Finset.card_map, Finset.card_univ, Fintype.card_fin] at this
  exact_mod_cast this

/-- `tendsto_measure_abs_heEstimate_sub_ge` applies to the sequence: all hypotheses hold. -/
example {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => Measure.dirac () {ω | ε ≤
      |heEstimate (grm (Xn n)) (fun i => (Dn n).pheno (Xn n) i ω) - 1|}) atTop (𝓝 0) :=
  tendsto_measure_abs_heEstimate_sub_ge (μ := fun _ => Measure.dirac ())
    Dn Xn (C := 0) (fun _ => rfl) (fun _ _ _ => MemLp.of_discrete)
    (fun n p _ => by simp [heDev_Dn])
    (tendsto_atTop_mono le_sum_grm_Xn tendsto_natCast_atTop_atTop) hε

/-- Directly: the estimator is exactly `h² = 1` for every `n ≥ 1`. -/
example (n : ℕ) (ω : Unit) :
    heEstimate (grm (Xn (n + 1))) (fun i => (Dn (n + 1)).pheno (Xn (n + 1)) i ω) = 1 := by
  have hS : ∑ p ∈ pairs (n + 2), grm (Xn (n + 1)) p.1 p.2 ^ 2 ≠ 0 := by
    have := le_sum_grm_Xn (n + 1); push_cast at this; linarith
  have h := heEstimate_sub (grm (Xn (n + 1)))
    (fun i => (Dn (n + 1)).pheno (Xn (n + 1)) i ω) hS 1
  have h0 : ∀ p ∈ pairs (n + 2), grm (Xn (n + 1)) p.1 p.2 *
      ((Dn (n + 1)).pheno (Xn (n + 1)) p.1 ω * (Dn (n + 1)).pheno (Xn (n + 1)) p.2 ω -
        1 * grm (Xn (n + 1)) p.1 p.2) = 0 := fun p _ => by
    simp [grm_Xn, LDScore.Model.pheno, Dn, Xn]
  rw [Finset.sum_eq_zero h0, zero_div, sub_eq_zero] at h
  exact h

end MathlibExtTest.Biology.StatisticalGenetics.GREML

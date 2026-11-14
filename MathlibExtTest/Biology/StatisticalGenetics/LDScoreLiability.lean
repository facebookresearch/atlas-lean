/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.LDScoreLiability
import MathlibExt.Probability.Distributions.GaussianCdf

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real
open MathlibExt.Biology.StatisticalGenetics.LDScore
  MathlibExt.Biology.StatisticalGenetics.LDScoreInflation
  MathlibExt.Biology.StatisticalGenetics.LDScoreRegression
  MathlibExt.Biology.StatisticalGenetics.LDScoreLiability
  MathlibExt.Probability.FiniteProbability

namespace MathlibExtTest.Biology.StatisticalGenetics.LDScoreLiability

/-! ### Threshold quantities at `t = 0`, computed from the definitions -/

/-- Threshold `0` gives prevalence `K = Φ(0) = 1/2`. -/
theorem prevalence_zero : prevalence 0 = 1 / 2 := by
  simp [prevalence, cdf_gaussianReal_zero]

/-- `φ(0)² = 1 / (2π)`. -/
theorem thresholdDensity_zero_sq : thresholdDensity 0 ^ 2 = 1 / (2 * π) := by
  have h : thresholdDensity 0 = (√(2 * π))⁻¹ := by simp [thresholdDensity, gaussianPDFReal]
  rw [h, inv_pow, Real.sq_sqrt (by positivity), one_div]

/-- The Dempster–Lerner factor at `K = 1/2` is `K (1 - K) / z² = π / 2`. -/
example : popLiabilityFactor 0 = π / 2 := by
  rw [popLiabilityFactor, prevalence_zero, thresholdDensity_zero_sq]
  field_simp
  ring

/-- Sampling cases at their population frequency (`P = K = 1/2`) gives the same factor `π / 2`,
computed from the definition of the case-control factor. -/
example : ccLiabilityFactor 0 (1 / 2) = π / 2 := by
  rw [ccLiabilityFactor, prevalence_zero, thresholdDensity_zero_sq]
  field_simp
  ring

/-- Over- or under-sampling cases changes the factor: with `P = 1/4`, it is `2π / 3`. -/
example : ccLiabilityFactor 0 (1 / 4) = 2 * π / 3 := by
  rw [ccLiabilityFactor, prevalence_zero, thresholdDensity_zero_sq]
  field_simp
  ring

/-- Boundary: with no cases or no controls (`P ∈ {0, 1}`) the factor is the junk value `0`. -/
example (t : ℝ) : ccLiabilityFactor t 0 = 0 ∧ ccLiabilityFactor t 1 = 0 := by
  simp [ccLiabilityFactor]

/-- Boundary: equal LD scores leave the slope unidentified, so the liability-scale estimate is
the junk value `0`. -/
example : liabilityH2Hat 0 (1 / 4) 4 3 ![1, 1, 1] ![1, 5, 9] = 0 := by
  simp [liabilityH2Hat, olsH2Hat, olsSlope, sxy, sampleMean_eq_sum_div, Fin.sum_univ_three]
  norm_num

/-! ### A Gaussian liability model with `h² = 1/2`

On `ℝ × ℝ` with the product of two standard normal laws, the liability is the first coordinate
`L = x` and the genetic value is `G = (x + y) / 2`, so `Var G = Cov(G, L) = 1/2`. (Equivalently
`L = G + E` with `E = (x - y) / 2` independent of `G`.) Every hypothesis is checked from the
definitions. -/

/-- Product of two standard normal laws. -/
noncomputable def μ2 : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

instance : IsProbabilityMeasure μ2 := by
  unfold μ2
  infer_instance

theorem hasLaw_fst : HasLaw Prod.fst (gaussianReal 0 1) μ2 :=
  ⟨measurable_fst.aemeasurable, by rw [μ2, Measure.map_fst_prod, measure_univ, one_smul]⟩

theorem hasLaw_snd : HasLaw Prod.snd (gaussianReal 0 1) μ2 :=
  ⟨measurable_snd.aemeasurable, by rw [μ2, Measure.map_snd_prod, measure_univ, one_smul]⟩

/-- The genetic value `G = (x + y) / 2`. -/
noncomputable def G : ℝ × ℝ → ℝ := fun p => (p.1 + p.2) / 2

theorem G_eq : G = (1 / 2 : ℝ) • Prod.fst + (1 / 2 : ℝ) • Prod.snd := by
  ext p
  simp [G]
  ring

theorem hasGaussianLaw_G_fst : HasGaussianLaw (fun p => (G p, p.1)) μ2 := by
  let T : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    ((1 / 2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (1 / 2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have h : HasGaussianLaw id μ2 := by
    unfold μ2
    exact IsGaussian.hasGaussianLaw_id
  exact (h.map_fun T).congr (ae_of_all _ fun p => by simp [T, G]; ring)

theorem memLp_fst : MemLp (Prod.fst : ℝ × ℝ → ℝ) 2 μ2 := memLp_of_hasLaw_std hasLaw_fst

theorem memLp_snd : MemLp (Prod.snd : ℝ × ℝ → ℝ) 2 μ2 := memLp_of_hasLaw_std hasLaw_snd

theorem cov_fst_snd : cov[Prod.fst, Prod.snd; μ2] = 0 :=
  covariance_fst_snd_prod (X := id) (Y := id) (memLp_id_gaussianReal 2) (memLp_id_gaussianReal 2)

theorem cov_fst_fst : cov[Prod.fst, Prod.fst; μ2] = 1 := by
  rw [covariance_self measurable_fst.aemeasurable, variance_of_hasLaw_std hasLaw_fst]

theorem cov_snd_snd : cov[Prod.snd, Prod.snd; μ2] = 1 := by
  rw [covariance_self measurable_snd.aemeasurable, variance_of_hasLaw_std hasLaw_snd]

theorem cov_G_fst : cov[G, Prod.fst; μ2] = 1 / 2 := by
  rw [G_eq, covariance_add_left (memLp_fst.const_smul _) (memLp_snd.const_smul _) memLp_fst,
    covariance_smul_left, covariance_smul_left, cov_fst_fst, covariance_comm, cov_fst_snd]
  norm_num

theorem var_G : Var[G; μ2] = 1 / 2 := by
  have hGm : AEMeasurable G μ2 := ((measurable_fst.add measurable_snd).div_const 2).aemeasurable
  rw [← covariance_self hGm]
  have hG2 : MemLp G 2 μ2 := by
    rw [G_eq]
    exact (memLp_fst.const_smul _).add (memLp_snd.const_smul _)
  rw [G_eq] at hG2 ⊢
  rw [covariance_add_left (memLp_fst.const_smul _) (memLp_snd.const_smul _) hG2,
    covariance_add_right (memLp_fst.const_smul _) (memLp_fst.const_smul _)
      (memLp_snd.const_smul _),
    covariance_add_right (memLp_snd.const_smul _) (memLp_fst.const_smul _)
      (memLp_snd.const_smul _)]
  simp only [covariance_smul_left, covariance_smul_right]
  rw [cov_fst_fst, cov_snd_snd, cov_fst_snd, covariance_comm, cov_fst_snd]
  norm_num

/-- Non-vacuity of the liability threshold hypotheses, and Dempster–Lerner at `K = 1/2`: the
observed-scale heritability of `h² = 1/2` is `h² z² / (K (1 - K)) = 1 / π`. -/
example : corrSq μ2 G (caseInd Prod.fst 0) = 1 / π := by
  rw [corrSq_genetic_caseInd hasGaussianLaw_G_fst hasLaw_fst measurable_fst 0 var_G cov_G_fst,
    prevalence_zero, thresholdDensity_zero_sq]
  field_simp
  ring

/-- The Dempster–Lerner conversion recovers `h² = 1/2` from the observed scale. -/
example : popLiabilityFactor 0 * corrSq μ2 G (caseInd Prod.fst 0) = 1 / 2 :=
  (h2_eq_popLiabilityFactor_mul hasGaussianLaw_G_fst hasLaw_fst measurable_fst 0 var_G
    cov_G_fst).symm

/-- The case-control law with `P = K` is the population law. -/
example : caseControl μ2 Prod.fst 0 (μ2.real {p | 0 ≤ p.1}) = μ2 := by
  have hk := measureReal_case hasLaw_fst 0
  exact caseControl_prevalence measurable_fst (hk ▸ prevalence_pos 0)
    (hk ▸ prevalence_lt_one 0)

/-- With `P = 1/4`, cases have mass `1/4` in the case-control law. -/
example : (caseControl μ2 Prod.fst 0 (1 / 4)).real {p | 0 ≤ p.1} = 1 / 4 := by
  have hk := measureReal_case hasLaw_fst 0
  exact measureReal_case_caseControl measurable_fst (by norm_num) (by norm_num)
    (hk ▸ prevalence_pos 0) (hk ▸ prevalence_lt_one 0)

/-- The case-control proxy with `P = 1/2 = K` is `1 / π`. -/
theorem caseControlH2Proxy_half : caseControlH2Proxy μ2 Prod.fst G 0 (1 / 2) = 1 / π := by
  rw [caseControlH2Proxy_genetic hasGaussianLaw_G_fst hasLaw_fst measurable_fst (by norm_num)
    (by norm_num) var_G cov_G_fst, prevalence_zero, thresholdDensity_zero_sq]
  field_simp
  ring

/-- Oversampling controls (`P = 1/4`) changes the proxy to `3 / (4π)`. -/
example : caseControlH2Proxy μ2 Prod.fst G 0 (1 / 4) = 3 / (4 * π) := by
  rw [caseControlH2Proxy_genetic hasGaussianLaw_G_fst hasLaw_fst measurable_fst (by norm_num)
    (by norm_num) var_G cov_G_fst, prevalence_zero, thresholdDensity_zero_sq]
  field_simp
  ring

/-! ### An observed-scale LD-score model with heritability `1 / π`

`N = 4`, `M = 3` on `Fin 8` with the uniform probability measure, as in the `LDScoreRegression`
test, with the effects and noise scaled to second moments `h² / 3` and `1 - h²`. -/

/-- The uniform probability measure on `Fin 8`. -/
noncomputable def μ8 : Measure (Fin 8) := (8⁻¹ : ℝ≥0∞) • Measure.count

instance : IsProbabilityMeasure μ8 :=
  ⟨by simpa [μ8] using ENNReal.inv_mul_cancel (by norm_num : (8 : ℝ≥0∞) ≠ 0) (by norm_num)⟩

theorem integral_μ8 (f : Fin 8 → ℝ) :
    ∫ ω, f ω ∂μ8 = (f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7) / 8 := by
  simp only [μ8, integral_smul_measure, integral_count, Fin.sum_univ_eight]
  norm_num
  ring

/-- The non-constant Walsh functions on `Fin 8`. -/
def walsh : Fin 7 → Fin 8 → ℝ :=
  ![![1, -1, 1, -1, 1, -1, 1, -1], ![1, 1, -1, -1, 1, 1, -1, -1],
    ![1, -1, -1, 1, 1, -1, -1, 1], ![1, 1, 1, 1, -1, -1, -1, -1],
    ![1, -1, 1, -1, -1, 1, -1, 1], ![1, 1, -1, -1, -1, -1, 1, 1],
    ![1, -1, -1, 1, -1, 1, 1, -1]]

theorem walsh_orth (i j : Fin 7) :
    ∫ ω, walsh i ω * walsh j ω ∂μ8 = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [integral_μ8, walsh] <;> norm_num

theorem integral_walsh (i : Fin 7) : ∫ ω, walsh i ω ∂μ8 = 0 := by
  fin_cases i <;> simp [integral_μ8, walsh]

theorem integral_scaled (a b : ℝ) (i j : Fin 7) :
    ∫ ω, a * walsh i ω * (b * walsh j ω) ∂μ8 = a * b * (if i = j then 1 else 0) := by
  rw [← walsh_orth, ← integral_const_mul]
  congr 1
  funext ω
  ring

/-- Walsh indices of the effects. -/
def bIdx (k : Fin 3) : Fin 7 := Fin.castLE (by norm_num) k

/-- Walsh indices of the noise terms. -/
def eIdx (i : Fin 4) : Fin 7 := Fin.natAdd 3 i

theorem bIdx_inj {k l : Fin 3} : bIdx k = bIdx l ↔ k = l :=
  ⟨fun h => Fin.castLE_injective _ h, fun h => h ▸ rfl⟩

theorem eIdx_inj {i i' : Fin 4} : eIdx i = eIdx i' ↔ i = i' :=
  ⟨fun h => Fin.natAdd_injective _ _ h, fun h => h ▸ rfl⟩

theorem bIdx_ne_eIdx (k : Fin 3) (i : Fin 4) : bIdx k ≠ eIdx i := by
  intro h
  have := congrArg Fin.val h
  simp [bIdx, eIdx] at this
  omega

/-- The observed-scale model with heritability `h ∈ [0, 1]`. -/
noncomputable def Dh (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) : Model μ8 4 3 where
  h2 := h
  beta := fun k ω => √(h / 3) * walsh (bIdx k) ω
  eps := fun i ω => √(1 - h) * walsh (eIdx i) ω
  memLp_beta := fun _ => MemLp.of_discrete
  memLp_eps := fun _ => MemLp.of_discrete
  integral_beta_mul := by
    intro k l
    show ∫ ω, √(h / 3) * walsh (bIdx k) ω * (√(h / 3) * walsh (bIdx l) ω) ∂μ8 = _
    rw [integral_scaled, ← sq, Real.sq_sqrt (by positivity)]
    by_cases hkl : k = l
    · subst hkl
      simp
    · simp [hkl, bIdx_inj]
  integral_eps_mul := by
    intro i i'
    show ∫ ω, √(1 - h) * walsh (eIdx i) ω * (√(1 - h) * walsh (eIdx i') ω) ∂μ8 = _
    rw [integral_scaled, ← sq, Real.sq_sqrt (by linarith)]
    by_cases hii : i = i'
    · subst hii
      simp
    · simp [hii, eIdx_inj]
  integral_beta_mul_eps := by
    intro k i
    show ∫ ω, √(h / 3) * walsh (bIdx k) ω * (√(1 - h) * walsh (eIdx i) ω) ∂μ8 = 0
    rw [integral_scaled]
    simp [bIdx_ne_eIdx]

theorem inv_pi_le_one : 1 / π ≤ 1 := by
  rw [div_le_one Real.pi_pos]
  linarith [Real.two_le_pi]

/-- The observed-scale model with heritability `1 / π`. -/
noncomputable def Dπ : Model μ8 4 3 := Dh (1 / π) (by positivity) inv_pi_le_one

theorem hβ : ∀ k, ∫ ω, Dπ.beta k ω ∂μ8 = 0 := fun k => by
  show ∫ ω, √(1 / π / 3) * walsh (bIdx k) ω ∂μ8 = 0
  rw [integral_const_mul, integral_walsh, mul_zero]

theorem hε : ∀ i, ∫ ω, Dπ.eps i ω ∂μ8 = 0 := fun i => by
  show ∫ ω, √(1 - 1 / π) * walsh (eIdx i) ω ∂μ8 = 0
  rw [integral_const_mul, integral_walsh, mul_zero]

/-- Three standardized markers: the first two identical, the third orthogonal to them. -/
def X : Matrix (Fin 4) (Fin 3) ℝ := !![1, 1, 1; 1, 1, -1; -1, -1, 1; -1, -1, -1]

theorem isStandardized_X : IsStandardized X := by
  intro k
  fin_cases k <;> simp [X, Fin.sum_univ_four] <;> norm_num

/-- The LD scores are `(2, 2, 1)`, computed from the definition. -/
theorem ldScore_X : ldScore X = ![2, 2, 1] := by
  funext j
  fin_cases j <;> simp [ldScore, ldCorr, X, Fin.sum_univ_four, Fin.sum_univ_three] <;> norm_num

theorem sxy_ldScore_X : sxy (ldScore X) (ldScore X) ≠ 0 := by
  rw [ldScore_X]
  simp [sxy, sampleMean_eq_sum_div, Fin.sum_univ_three]
  norm_num

/-- A stratification term common to all markers, `a = 1/16`. -/
theorem ha : ∀ j, (1 : ℝ) ^ 2 * ((∑ i, X i j * (![1, 0, 0, 0] : Fin 4 → ℝ) i) /
    ((4 : ℕ) : ℝ)) ^ 2 = 1 / 16 := by
  intro j
  fin_cases j <;> simp [X, Fin.sum_univ_four] <;> norm_num

/-- The bridging hypothesis holds for the witnesses: the observed-scale model's heritability is
the case-control proxy of the liability model with `P = 1/2`. -/
theorem hobs : Dπ.h2 = caseControlH2Proxy μ2 Prod.fst G 0 (1 / 2) := by
  rw [caseControlH2Proxy_half]
  rfl

/-- Non-vacuity of the liability-scale LD-score regression theorems: population consistency
returns the liability heritability `1/2`. -/
example : liabilityH2Hat 0 (1 / 2) 4 3 (ldScore X)
    (fun j => ∫ ω, chiSqStrat Dπ X 1 ![1, 0, 0, 0] j ω ∂μ8) = 1 / 2 :=
  liabilityH2Hat_integral_chiSqStrat hasGaussianLaw_G_fst hasLaw_fst measurable_fst
    (by norm_num) (by norm_num) var_G cov_G_fst Dπ hobs X (by norm_num) (by norm_num)
    isStandardized_X sxy_ldScore_X hβ hε 1 _ ha

/-- Unbiasedness: `𝔼[ĥ²_l] = 1/2` despite the confounding term. -/
example : ∫ ω, liabilityH2Hat 0 (1 / 2) 4 3 (ldScore X)
    (fun j => chiSqStrat Dπ X 1 ![1, 0, 0, 0] j ω) ∂μ8 = 1 / 2 :=
  integral_liabilityH2Hat_chiSqStrat hasGaussianLaw_G_fst hasLaw_fst measurable_fst
    (by norm_num) (by norm_num) var_G cov_G_fst Dπ hobs X (by norm_num) (by norm_num)
    isStandardized_X sxy_ldScore_X hβ hε 1 _ ha

/-- Without the conversion, the observed-scale estimate is `1 / π`, not the liability `1/2`:
the observed scale understates the liability heritability here. -/
example : ∫ ω, olsH2Hat 4 3 (ldScore X) (fun j => chiSqStrat Dπ X 1 ![1, 0, 0, 0] j ω) ∂μ8 =
    1 / π :=
  integral_olsH2Hat_chiSqStrat Dπ X (by norm_num) (by norm_num) isStandardized_X sxy_ldScore_X
    hβ hε 1 _ ha

#print axioms covariance_caseInd
#print axioms corrSq_caseInd
#print axioms h2_eq_popLiabilityFactor_mul
#print axioms covariance_caseControl
#print axioms h2_eq_ccLiabilityFactor_mul
#print axioms integral_liabilityH2Hat_chiSqStrat
#print axioms tendstoInMeasure_liabilityH2Hat

end MathlibExtTest.Biology.StatisticalGenetics.LDScoreLiability

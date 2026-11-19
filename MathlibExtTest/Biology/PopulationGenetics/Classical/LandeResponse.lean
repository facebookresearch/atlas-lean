/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Classical.LandeResponse
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# Tests for Lande's multivariate response

The examples check that the integrability hypothesis excludes a weight with finite mean
fitness but no selected mean, that the cross-covariance hypothesis is a real restriction,
the record-form hypotheses, and a non-vacuity witness.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Finset

namespace MathlibExtTest.Biology.PopulationGenetics.Classical.LandeResponse

open MathlibExt.Biology.PopulationGenetics.Classical.LandeResponse

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ### Extra checks: acceptance items, record-form hypotheses, non-vacuity -/

section Reviewer

open Real Set

/-- The reviewer's weight `W(z) = e^{z²/2} / (1 + z²)`. -/
private noncomputable def reviewerW (z : ℝ) : ℝ := exp (z ^ 2 / 2) / (1 + z ^ 2)

private lemma pdf_mul_reviewerW (x : ℝ) :
    gaussianPDFReal 0 1 x * reviewerW x = (√(2 * π))⁻¹ * (1 + x ^ 2)⁻¹ := by
  have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  simp only [gaussianPDFReal, reviewerW, NNReal.coe_one, mul_one, sub_zero]
  have hexp : exp (-x ^ 2 / 2) * exp (x ^ 2 / 2) = 1 := by
    rw [← exp_add, show -x ^ 2 / 2 + x ^ 2 / 2 = 0 by ring, exp_zero]
  calc (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) * (exp (x ^ 2 / 2) / (1 + x ^ 2))
      = (√(2 * π))⁻¹ * (exp (-x ^ 2 / 2) * exp (x ^ 2 / 2)) * (1 + x ^ 2)⁻¹ := by ring
    _ = (√(2 * π))⁻¹ * (1 + x ^ 2)⁻¹ := by rw [hexp, mul_one]

private lemma integrable_gaussian_iff {f : ℝ → ℝ} :
    Integrable f (gaussianReal 0 1) ↔ Integrable (fun x => gaussianPDFReal 0 1 x * f x) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero, gaussianPDF_def,
    integrable_withDensity_iff_integrable_smul' (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), smul_eq_mul]


-- acceptance 1: the reviewer's weight `W(z) = e^{z²/2}/(1 + z²)` with `Z ~ N(0, 1)` has finite mean
-- fitness but `𝔼[W(Z) Z]` does not exist, so the integrability hypothesis (`hWZ`) excludes it
example : Integrable reviewerW (gaussianReal 0 1) := by
  rw [integrable_gaussian_iff]
  simp_rw [pdf_mul_reviewerW]
  exact integrable_inv_one_add_sq.const_mul _

example : ¬ Integrable (fun z => reviewerW z * z) (gaussianReal 0 1) := by
  rw [integrable_gaussian_iff]
  intro h
  have hc : (0 : ℝ) < (√(2 * π))⁻¹ := by positivity
  have he : ∀ x, gaussianPDFReal 0 1 x * (reviewerW x * x) = (√(2 * π))⁻¹ * (x / (1 + x ^ 2)) := by
    intro x
    rw [← mul_assoc, pdf_mul_reviewerW]; ring
  simp_rw [he] at h
  refine not_integrableOn_Ioi_inv (a := 1) ?_
  refine ((h.const_mul (2 / (√(2 * π))⁻¹)).integrableOn).mono' (by fun_prop) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun x hx => ?_)
  have hx1 : (1 : ℝ) < x := hx
  have hx0 : 0 < x := by linarith
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hx0)]
  have hq : (0 : ℝ) < 1 + x ^ 2 := by positivity
  rw [show 2 / (√(2 * π))⁻¹ * ((√(2 * π))⁻¹ * (x / (1 + x ^ 2))) = 2 * x / (1 + x ^ 2) by
    field_simp]
  rw [inv_eq_one_div, div_le_div_iff₀ hx0 hq]
  nlinarith


end Reviewer

-- acceptance 2: `Cov(A, Z) = G` is a real hypothesis. For `Z = 2A + ε` with `Cov(A, ε) = 0` the
-- cross-covariance is `2 Var(A)`, so `hG` with `G = Var(A)` fails unless `Var(A) = 0`
example [IsProbabilityMeasure P] {A ε : Ω → ℝ} (hA : MemLp A 2 P) (hε : MemLp ε 2 P)
    (h0 : cov[A, ε; P] = 0) : cov[A, fun ω => 2 * A ω + ε ω; P] = 2 * Var[A; P] := by
  change cov[A, (fun ω => 2 * A ω) + ε; P] = _
  rw [covariance_add_right hA (hA.const_mul 2) hε, covariance_const_mul_right, h0, add_zero,
    covariance_self hA.aemeasurable]

-- ... while the record's model `Z = A + E` with `Cov(A, E) = 0` gives `Cov(A, Z) = Var(A) = G`
example [IsProbabilityMeasure P] {A E : Ω → ℝ} (hA : MemLp A 2 P) (hE : MemLp E 2 P)
    (h0 : cov[A, E; P] = 0) : cov[A, fun ω => A ω + E ω; P] = Var[A; P] := by
  change cov[A, A + E; P] = _
  rw [covariance_add_right hA hA hE, h0, add_zero, covariance_self hA.aemeasurable]

-- acceptance 3: with `Var(A) = V_A`, the univariate statement is the breeder's
-- equation `R = h² S` with `h² = V_A / V_P`
example {A Z : Ω → ℝ} {Va Vp : ℝ} {W : ℝ → ℝ}
    (hAZ : HasGaussianLaw (fun ω => (A ω, Z ω)) P) (hG : cov[A, Z; P] = Va)
    (_hVa : Var[A; P] = Va) (hPZ : Var[Z; P] = Vp)
    (hVp : 0 < Vp) (hWm : Measurable W) (_hW0 : ∀ z, 0 ≤ W z) (hw : 0 < ∫ ω, W (Z ω) ∂P)
    (hWZ : Integrable (fun ω => W (Z ω) * Z ω) P) (hWA : Integrable (fun ω => W (Z ω) * A ω) P) :
    let S := (∫ ω, W (Z ω) * Z ω ∂P) / (∫ ω, W (Z ω) ∂P) - ∫ ω, Z ω ∂P
    let R := (∫ ω, W (Z ω) * A ω ∂P) / (∫ ω, W (Z ω) ∂P) - ∫ ω, A ω ∂P
    R = (Va / Vp) * S :=
  breeding_response_univariate_of_var hAZ hG _hVa hPZ hVp hWm _hW0 hw hWZ hWA

-- record-form hypotheses (`Var(A) = G`, `Cov(A, Z) = G`, `W ≥ 0`, `0 < 𝔼 W(Z)`) are the
-- genetic-covariance form of Lande's response
example {A Z : Ω → ι → ℝ} {G Pm : Matrix ι ι ℝ} {W : (ι → ℝ) → ℝ}
    (hAZ : HasGaussianLaw (fun ω => (A ω, Z ω)) P)
    (hG : ∀ i j, cov[fun ω => A ω i, fun ω => Z ω j; P] = G i j)
    (_hGA : ∀ i j, cov[fun ω => A ω i, fun ω => A ω j; P] = G i j)
    (hPZ : ∀ i j, cov[fun ω => Z ω i, fun ω => Z ω j; P] = Pm i j) (hPd : Pm.PosDef)
    (hWm : Measurable W) (_hW0 : ∀ z, 0 ≤ W z) (hw : 0 < ∫ ω, W (Z ω) ∂P)
    (hWZ : ∀ j, Integrable (fun ω => W (Z ω) * Z ω j) P)
    (hWA : ∀ i, Integrable (fun ω => W (Z ω) * A ω i) P) :
    selectedShift W Z A P = (G * Pm⁻¹) *ᵥ selectedShift W Z Z P :=
  selectedShift_breeding_eq_geneticCov hAZ hG _hGA hPZ hPd hWm _hW0 hw hWZ hWA

-- non-vacuity: `A = Z ~ N(0, 1)` (heritability one) satisfies every hypothesis with `W = 1`
example : HasGaussianLaw (fun x : ℝ => (x, x)) (gaussianReal 0 1) :=
  IsGaussian.hasGaussianLaw_id.map_fun ((ContinuousLinearMap.id ℝ ℝ).prod (ContinuousLinearMap.id ℝ ℝ))
example : cov[fun x : ℝ => x, fun x => x; gaussianReal 0 1] = 1 := by
  rw [covariance_self aemeasurable_id', variance_fun_id_gaussianReal]; rfl
example : ∫ x, (fun _ : ℝ => (1 : ℝ)) x ∂(gaussianReal 0 1) ≠ 0 := by simp

#print axioms selectedShift_breeding_eq
#print axioms selectedShift_breeding_eq_geneticCov
#print axioms breeding_response_univariate
#print axioms breeding_response_univariate_of_var
#print axioms selectedShift_breeding_eq_gradient
#print axioms selectedShift_breeding_eq_gradient_geneticCov

end MathlibExtTest.Biology.PopulationGenetics.Classical.LandeResponse

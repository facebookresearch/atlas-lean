/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.StatisticalGenetics.SmithHazelIndex
public import Domains.Biology.StatisticalGenetics.SmithHazel
public import MathlibExt.Probability.Causality.MissingData.GaussianSelection
public import MathlibExt.Probability.Distributions.GaussianCdf
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! # Smith–Hazel truncation tests

Checks the selected proportion, the intensity of selection and the standardization of a Gaussian
index score for an explicit model.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix SmithHazel
open MathlibExt.Probability.Causality.MissingData (inverseMillsRatio)
open scoped Matrix RealInnerProductSpace

namespace SmithHazel.TailTest

abbrev P : Matrix (Fin 2) (Fin 2) ℝ := !![(3 : ℝ), 1; 1, 3]
abbrev a : Fin 2 → ℝ := ![(1 : ℝ), 0]

abbrev Latents := EuclideanSpace ℝ (Fin 5)
noncomputable abbrev γ : Measure Latents := stdGaussian Latents

noncomputable def loading (u : Fin 5 → ℝ) : Latents →L[ℝ] ℝ :=
  innerSL ℝ (WithLp.toLp 2 u)

theorem loading_cov (u v : Fin 5 → ℝ) :
    cov[loading u, loading v; γ] = u ⬝ᵥ v := by
  change cov[fun x => ⟪WithLp.toLp 2 u, x⟫, fun x => ⟪WithLp.toLp 2 v, x⟫; γ] = u ⬝ᵥ v
  rw [← covarianceBilin_apply_eq_cov
    (IsGaussian.hasGaussianLaw_id (μ := γ)).memLp_two,
    covarianceBilin_stdGaussian, innerSL_apply_apply, PiLp.inner_apply, dotProduct]
  simp only [RCLike.inner_apply, conj_trivial, mul_comm]

theorem loading_memLp (u : Fin 5 → ℝ) : MemLp (loading u) 2 γ :=
  (IsGaussian.hasGaussianLaw_id.map_fun (loading u)).memLp_two

abbrev additiveLoading : Fin 2 → Fin 5 → ℝ :=
  ![![(1 : ℝ), 1, 0, 0, 0], ![1, 0, 1, 0, 0]]

abbrev residualLoading : Fin 2 → Fin 5 → ℝ :=
  ![![(0 : ℝ), 0, 0, 1, 0], ![0, 0, 0, 0, 1]]

noncomputable def additiveScore : Latents →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi fun i => loading (additiveLoading i)

noncomputable def residualScore : Latents →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi fun i => loading (residualLoading i)

theorem phenotypeScore (i : Fin 2) :
    (fun x => additiveScore x i + residualScore x i) =
      loading (additiveLoading i + residualLoading i) := by
  funext x
  change ⟪WithLp.toLp 2 (additiveLoading i), x⟫ + ⟪WithLp.toLp 2 (residualLoading i), x⟫ =
    ⟪WithLp.toLp 2 (additiveLoading i + residualLoading i), x⟫
  exact (inner_add_left _ _ _).symm

theorem twoTrait_phenotypeCov :
    (fun i j => cov[fun x => additiveScore x i + residualScore x i,
      fun x => additiveScore x j + residualScore x j; γ]) = P := by
  ext i j
  rw [phenotypeScore, phenotypeScore, loading_cov]
  fin_cases i <;> fin_cases j <;> norm_num [P, dotProduct, Fin.sum_univ_succ]

theorem P_posDef : P.PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [P, Matrix.conjTranspose_apply]
  · intro x hx
    change 0 < x ⬝ᵥ (P *ᵥ x)
    simp [P, mulVec, dotProduct, Fin.sum_univ_two]
    have h : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra! h
      apply hx
      funext i
      fin_cases i
      · exact h.1
      · exact h.2
    rcases h with h | h <;>
      nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 0 + x 1)]

noncomputable def twoTrait : Model 2 Latents γ where
  additive := additiveScore
  residual := residualScore
  economic := a
  measurable_additive := additiveScore.continuous.measurable
  measurable_residual := residualScore.continuous.measurable
  memLp_additive i := loading_memLp (additiveLoading i)
  memLp_residual i := loading_memLp (residualLoading i)
  orthogonal i j := by
    change cov[loading (additiveLoading i), loading (residualLoading j); γ] = 0
    rw [loading_cov]
    fin_cases i <;> fin_cases j <;> norm_num [dotProduct, Fin.sum_univ_succ]
  posDef := twoTrait_phenotypeCov ▸ P_posDef

theorem twoTrait_joint :
    HasGaussianLaw (fun x => (twoTrait.additive x, twoTrait.residual x)) γ :=
  IsGaussian.hasGaussianLaw_id.map_fun (additiveScore.prod residualScore)

noncomputable abbrev weights : Fin 2 → ℝ := ![(5 : ℝ) / 8, 1 / 8]

theorem weights_nontrivial : weights 0 ≠ 0 ∧ weights 1 ≠ 0 := by
  norm_num [weights]

theorem aggregate_index_gaussian :
    HasGaussianLaw (fun x => (twoTrait.aggregate x, twoTrait.index weights x)) γ :=
  SmithHazel.hasGaussianLaw_aggregate_index twoTrait twoTrait_joint weights

noncomputable abbrev ν : Measure ℝ := gaussianReal 0 1
def score (x : ℝ) : ℝ := 2 + 3 * x

theorem standard_hasLaw : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) ν :=
  ⟨measurable_id.aemeasurable, Measure.map_id⟩

theorem score_measurable : Measurable score :=
  measurable_const.add (measurable_const.mul measurable_id)

theorem score_gaussian : HasGaussianLaw score ν := by
  exact (gaussianReal_const_add (gaussianReal_const_mul standard_hasLaw 3) 2).hasGaussianLaw

theorem score_variance : Var[score; ν] = 9 := by
  change Var[(fun x : ℝ => 2 + 3 * x); ν] = 9
  rw [variance_const_add (X := fun x : ℝ => 3 * x)
    (measurable_id.const_mul 3).aestronglyMeasurable,
    variance_const_mul, variance_fun_id_gaussianReal]
  norm_num

theorem score_variance_pos : 0 < Var[score; ν] := by
  rw [score_variance]
  norm_num

theorem standardized_score_law :
    HasLaw (standardizedValue ν score) (gaussianReal 0 1) ν :=
  ProbabilityTheory.hasLaw_standardizedValue score_gaussian score_variance_pos

theorem median_event_measure :
    ν.real (standardizedUpperEvent ν score 0) = 1 / 2 := by
  rw [ProbabilityTheory.measureReal_standardizedUpperEvent score_gaussian score_variance_pos,
    neg_zero, cdf_gaussianReal_zero]

theorem nonzero_event_measure :
    ν.real (standardizedUpperEvent ν score 1) = cdf (gaussianReal 0 1) (-1) :=
  ProbabilityTheory.measureReal_standardizedUpperEvent score_gaussian score_variance_pos 1

theorem positive_cut_tail_bounds :
    0 < cdf (gaussianReal 0 1) (-1) ∧ cdf (gaussianReal 0 1) (-1) < 1 := by
  have h := ProbabilityTheory.gaussianUpperTail_mem_Ioo 1
  exact ⟨h.1, h.2⟩

theorem negative_cut_tail_bounds :
    0 < cdf (gaussianReal 0 1) 1 ∧ cdf (gaussianReal 0 1) 1 < 1 := by
  have h := ProbabilityTheory.gaussianUpperTail_mem_Ioo (-1)
  simpa only [neg_neg] using And.intro h.1 h.2

theorem nonzero_conditional_integral :
    (∫ x, standardizedValue ν score x ∂ν[|standardizedUpperEvent ν score 1]) =
      inverseMillsRatio (-1) :=
  ProbabilityTheory.integral_cond_standardizedValue
    score_measurable score_gaussian score_variance_pos 1

theorem reflected_density_upper_tail :
    inverseMillsRatio (-1) =
      gaussianPDFReal 0 1 1 / cdf (gaussianReal 0 1) (-1) :=
  ProbabilityTheory.inverseMillsRatio_neg_eq_pdf_div_upperTail 1

theorem constant_score_variance : Var[(fun _ : ℝ => (2 : ℝ)); ν] = 0 := by
  have h := variance_const_add (X := fun _ : ℝ => 0) (μ := ν)
    measurable_const.aestronglyMeasurable (2 : ℝ)
  simpa only [add_zero, ← Pi.zero_def, variance_zero] using h

theorem constant_score_not_positive :
    ¬ 0 < Var[(fun _ : ℝ => (2 : ℝ)); ν] := by
  rw [constant_score_variance]
  exact lt_irrefl 0

#print axioms P
#print axioms a
#print axioms Latents
#print axioms γ
#print axioms loading
#print axioms loading_cov
#print axioms loading_memLp
#print axioms additiveLoading
#print axioms residualLoading
#print axioms additiveScore
#print axioms residualScore
#print axioms phenotypeScore
#print axioms twoTrait_phenotypeCov
#print axioms P_posDef
#print axioms twoTrait
#print axioms twoTrait_joint
#print axioms weights
#print axioms weights_nontrivial
#print axioms aggregate_index_gaussian
#print axioms ν
#print axioms score
#print axioms standard_hasLaw
#print axioms score_measurable
#print axioms score_gaussian
#print axioms score_variance
#print axioms score_variance_pos
#print axioms standardized_score_law
#print axioms median_event_measure
#print axioms nonzero_event_measure
#print axioms positive_cut_tail_bounds
#print axioms negative_cut_tail_bounds
#print axioms nonzero_conditional_integral
#print axioms reflected_density_upper_tail
#print axioms constant_score_variance
#print axioms constant_score_not_positive

end SmithHazel.TailTest

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Generative.ScoreDiffusion
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import MathlibExt.Probability.Distributions.GaussianDensity
public import MathlibExt.Probability.Distributions.GaussianShift

/-!
# Tests for score-based diffusion models: forward process and DDPM sampler

Closed-instance checks for `CSLibExt.MachineLearning.Generative.ScoreDiffusion` on concrete
Euclidean spaces: the forward law at time zero and from a point, stationarity, probability
measure inference, one sampler step from a point, sampler index discipline (which estimate each
step uses, and in which order), the Gaussian score and its Lipschitz constant, the score of
`N(0, I/4)` and its Lipschitz constants, the zero-dimensional case, and total variation distance
from a Dirac law.
-/

@[expose] public section

namespace Cslib.MachineLearning.ScoreDiffusionTests

open MeasureTheory ProbabilityTheory Cslib.MachineLearning.ScoreDiffusion

/-- The forward law at time zero on a Dirac input is the Dirac law. -/
theorem ouMarginal_zero_dirac (x : EuclideanSpace ℝ (Fin 2)) :
    ouMarginal (Measure.dirac x) 0 = Measure.dirac x :=
  ouMarginal_zero (Measure.dirac x)

/-- From a point `x`, the forward law at time `t ≥ 0` is `N(e^{-t} x, (1 - e^{-2t}) I)`
(Chen et al., arXiv:2209.11215v3, Section 2.1). -/
theorem ouMarginal_dirac (x : EuclideanSpace ℝ (Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    ouMarginal (Measure.dirac x) t =
      multivariateGaussian (Real.exp (-t) • x) ((1 - Real.exp (-2 * t)) • 1) := by
  have h1 : 0 ≤ 1 - Real.exp (-2 * t) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hS : (1 - Real.exp (-2 * t)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) =
      Real.sqrt (1 - Real.exp (-2 * t)) ^ 2 • 1 := by
    rw [Real.sq_sqrt h1]
  have hc : Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2 := by
    fun_prop
  rw [hS, ← stdGaussian_map_const_add_smul, ouMarginal, Measure.dirac_prod,
    Measure.map_map hc measurable_prodMk_left]
  rfl

/-- The standard Gaussian is stationary at time one on `EuclideanSpace ℝ (Fin 1)`. -/
theorem ouMarginal_stdGaussian_one :
    ouMarginal (stdGaussian (EuclideanSpace ℝ (Fin 1))) 1 =
      stdGaussian (EuclideanSpace ℝ (Fin 1)) :=
  ouMarginal_stdGaussian (by norm_num)

/-- The forward marginal of a probability law is inferred as a probability law. -/
theorem ouMarginal_isProbability (q : Measure (EuclideanSpace ℝ (Fin 1)))
    [IsProbabilityMeasure q] (t : ℝ) : IsProbabilityMeasure (ouMarginal q t) :=
  inferInstance

/-- One sampler step from a probability law is inferred as a probability law. -/
theorem ddpmStep_isProbability (h : ℝ)
    (σ : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1))
    (μ : Measure (EuclideanSpace ℝ (Fin 1))) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (ddpmStep h σ μ) :=
  inferInstance

/-- One sampler step from a point `x` with step `h ≥ 0` and a measurable estimate `σ` is the
Gaussian law `N(e^h x + 2 (e^h - 1) σ x, (e^{2h} - 1) I)`, the closed-form solution of equation
(2.8) of Chen et al. (arXiv:2209.11215v3) started at `x`. -/
theorem ddpmStep_dirac (σ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hσ : Measurable σ) (x : EuclideanSpace ℝ (Fin 2)) {h : ℝ} (hh : 0 ≤ h) :
    ddpmStep h σ (Measure.dirac x) =
      multivariateGaussian (Real.exp h • x + (2 * (Real.exp h - 1)) • σ x)
        ((Real.exp (2 * h) - 1) • 1) := by
  have h1 : 0 ≤ Real.exp (2 * h) - 1 := sub_nonneg.mpr (Real.one_le_exp (by linarith))
  have hS : (Real.exp (2 * h) - 1) • (1 : Matrix (Fin 2) (Fin 2) ℝ) =
      Real.sqrt (Real.exp (2 * h) - 1) ^ 2 • 1 := by
    rw [Real.sq_sqrt h1]
  have hc : Measurable fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      Real.exp h • p.1 + (2 * (Real.exp h - 1)) • σ p.1 +
        Real.sqrt (Real.exp (2 * h) - 1) • p.2 := by
    fun_prop
  rw [hS, ← stdGaussian_map_const_add_smul]
  unfold ddpmStep
  rw [Measure.dirac_prod, Measure.map_map hc measurable_prodMk_left]
  rfl

/-- The sampler output law is inferred as a probability law. -/
theorem ddpmOutput_isProbability (h : ℝ)
    (s : ℕ → EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) (N : ℕ) :
    IsProbabilityMeasure (ddpmOutput h s N) :=
  inferInstance

/-- A one-step run is one step from the standard Gaussian with the estimate `s 1`. -/
theorem ddpmOutput_one_check (h : ℝ)
    (s : ℕ → EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) :
    ddpmOutput h s 1 = ddpmStep h (s 1) (stdGaussian (EuclideanSpace ℝ (Fin 1))) :=
  ddpmOutput_one h s

/-- A two-step run uses the estimate `s 2` at time `2 h` in its first step and `s 1` in its last,
as the source's reverse-time discretization requires. -/
theorem ddpmOutput_two (h : ℝ)
    (s : ℕ → EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) :
    ddpmOutput h s 2 =
      ddpmStep h (s 1) (ddpmStep h (s 2) (stdGaussian (EuclideanSpace ℝ (Fin 1)))) :=
  rfl

/-- A two-step run is unchanged when only the estimate `s 0` is changed. -/
theorem ddpmOutput_two_congr (h : ℝ)
    (s : ℕ → EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1))
    (σ0 : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) :
    ddpmOutput h s 2 = ddpmOutput h (Function.update s 0 σ0) 2 := by
  refine ddpmOutput_congr h fun k hk => ?_
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have h0 : k ≠ 0 := by omega
  exact (Function.update_of_ne h0 σ0 s).symm

/-- The score of the standard Gaussian density on `Fin 2` is `fun x => -x`. -/
theorem logDensityScore_gaussian :
    logDensityScore (MetaMathlibExt.stdGaussianPDFReal (ι := Fin 2)) = fun x => -x := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hc : (0 : ℝ) < ((Real.sqrt (2 * Real.pi)) ^ Fintype.card (Fin 2))⁻¹ :=
    inv_pos.mpr (pow_pos (Real.sqrt_pos.mpr h2pi) _)
  have hlog : ∀ y : EuclideanSpace ℝ (Fin 2),
      Real.log (MetaMathlibExt.stdGaussianPDFReal y)
        = Real.log ((Real.sqrt (2 * Real.pi)) ^ Fintype.card (Fin 2))⁻¹ + (-(‖y‖ ^ 2) / 2) := by
    intro y
    unfold MetaMathlibExt.stdGaussianPDFReal
    rw [Real.log_mul (ne_of_gt hc) (Real.exp_ne_zero _), Real.log_exp]
  have hpt : ∀ y : EuclideanSpace ℝ (Fin 2),
      Real.log (MetaMathlibExt.stdGaussianPDFReal y)
        = Real.log ((Real.sqrt (2 * Real.pi)) ^ Fintype.card (Fin 2))⁻¹ + (-1 / 2) * ‖y‖ ^ 2 := by
    intro y
    rw [hlog y]
    ring
  have hgrad : ∀ x : EuclideanSpace ℝ (Fin 2),
      HasGradientAt (fun y => Real.log (MetaMathlibExt.stdGaussianPDFReal y)) (-x) x := by
    intro x
    have hbase : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖ ^ 2)
        (2 • innerSL ℝ x) x :=
      (hasStrictFDerivAt_norm_sq x).hasFDerivAt
    have hmul := hbase.const_mul (-1 / 2 : ℝ)
    have hadd := hmul.const_add (Real.log ((Real.sqrt (2 * Real.pi)) ^ Fintype.card (Fin 2))⁻¹)
    have hderiv : (-1 / 2 : ℝ) • (2 • innerSL ℝ x)
        = InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2)) (-x) := by
      ext y
      simp only [smul_apply, smul_eq_mul, innerSL_apply_apply,
        InnerProductSpace.toDual_apply_apply, inner_neg_left]
      ring
    rw [hderiv] at hadd
    have hnice : HasGradientAt
        (fun y : EuclideanSpace ℝ (Fin 2) =>
          Real.log ((Real.sqrt (2 * Real.pi)) ^ Fintype.card (Fin 2))⁻¹ + (-1 / 2) * ‖y‖ ^ 2)
        (-x) x :=
      hasGradientAt_iff_hasFDerivAt.mpr hadd
    have hfun :
        (fun y : EuclideanSpace ℝ (Fin 2) => Real.log (MetaMathlibExt.stdGaussianPDFReal y))
        = fun y => Real.log ((Real.sqrt (2 * Real.pi)) ^ Fintype.card (Fin 2))⁻¹
            + (-1 / 2) * ‖y‖ ^ 2 :=
      funext hpt
    rw [hfun]
    exact hnice
  unfold logDensityScore
  exact gradient_eq hgrad

/-- The Gaussian score on `Fin 2` is 1-Lipschitz. -/
theorem lipschitz_logDensityScore_gaussian :
    LipschitzWith 1 (logDensityScore (MetaMathlibExt.stdGaussianPDFReal (ι := Fin 2))) := by
  rw [logDensityScore_gaussian]
  exact LipschitzWith.id.neg

/-- Negated scaling by four is 4-Lipschitz on `EuclideanSpace ℝ (Fin 1)`. -/
private theorem lipschitz_neg_four_smul :
    LipschitzWith 4 (fun x : EuclideanSpace ℝ (Fin 1) => -(4 : ℝ) • x) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [dist_eq_norm]
  have hsub : (-(4 : ℝ)) • x - (-(4 : ℝ)) • y = (-(4 : ℝ)) • (x - y) :=
    (smul_sub _ _ _).symm
  rw [hsub, norm_smul, Real.norm_eq_abs]
  norm_num

/-- Negated scaling by four is not 1-Lipschitz on `EuclideanSpace ℝ (Fin 1)`. -/
private theorem not_lipschitz_neg_four_smul :
    ¬ LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin 1) => -(4 : ℝ) • x) := by
  intro hcon
  obtain ⟨a, b, hab⟩ := exists_pair_ne (EuclideanSpace ℝ (Fin 1))
  have hpos : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have hle := hcon.dist_le_mul a b
  simp only [dist_eq_norm] at hle
  rw [show (-(4 : ℝ)) • a - (-(4 : ℝ)) • b = (-(4 : ℝ)) • (a - b)
    from (smul_sub _ _ _).symm, norm_smul, Real.norm_eq_abs] at hle
  norm_num at hle
  linarith

/-- The score of the unnormalized density `x ↦ exp (-2 ‖x‖²)` of `N(0, I/4)` on
`EuclideanSpace ℝ (Fin 1)` is `x ↦ -4 x`. -/
theorem logDensityScore_exp_neg_two_mul_norm_sq :
    logDensityScore (fun x : EuclideanSpace ℝ (Fin 1) => Real.exp (-2 * ‖x‖ ^ 2)) =
      fun x => -(4 : ℝ) • x := by
  have hgrad : ∀ x : EuclideanSpace ℝ (Fin 1),
      HasGradientAt (fun y => Real.log (Real.exp (-2 * ‖y‖ ^ 2))) (-(4 : ℝ) • x) x := by
    intro x
    have hbase : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 1) => ‖y‖ ^ 2)
        (2 • innerSL ℝ x) x :=
      (hasStrictFDerivAt_norm_sq x).hasFDerivAt
    have hmul := hbase.const_mul (-2 : ℝ)
    have hderiv : (-2 : ℝ) • (2 • innerSL ℝ x)
        = InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 1)) (-(4 : ℝ) • x) := by
      ext y
      simp only [smul_apply, smul_eq_mul, innerSL_apply_apply,
        InnerProductSpace.toDual_apply_apply, real_inner_smul_left]
      ring
    rw [hderiv] at hmul
    simp only [Real.log_exp]
    exact hasGradientAt_iff_hasFDerivAt.mpr hmul
  unfold logDensityScore
  exact gradient_eq hgrad

/-- The score of `N(0, I/4)` is 4-Lipschitz: this law satisfies the Lipschitz-score assumption of
the sampling guarantee with `L = 4`. -/
theorem lipschitz_logDensityScore_exp_neg_two_mul_norm_sq :
    LipschitzWith 4
      (logDensityScore (fun x : EuclideanSpace ℝ (Fin 1) => Real.exp (-2 * ‖x‖ ^ 2))) := by
  rw [logDensityScore_exp_neg_two_mul_norm_sq]
  exact lipschitz_neg_four_smul

/-- The score of `N(0, I/4)` is not 1-Lipschitz, so the assumption fails for this law with
`L = 1`. -/
theorem not_lipschitz_logDensityScore_exp_neg_two_mul_norm_sq :
    ¬ LipschitzWith 1
      (logDensityScore (fun x : EuclideanSpace ℝ (Fin 1) => Real.exp (-2 * ‖x‖ ^ 2))) := by
  rw [logDensityScore_exp_neg_two_mul_norm_sq]
  exact not_lipschitz_neg_four_smul

/-- On `EuclideanSpace ℝ (Fin 0)` the sampler output agrees with any probability law. -/
theorem tvDist_ddpmOutput_dim_zero (q : Measure (EuclideanSpace ℝ (Fin 0)))
    [IsProbabilityMeasure q] (h : ℝ)
    (s : ℕ → EuclideanSpace ℝ (Fin 0) → EuclideanSpace ℝ (Fin 0)) (N : ℕ) :
    tvDist (ddpmOutput h s N) q = 0 := by
  have heq : ddpmOutput h s N = q := by
    refine Measure.ext fun t _ => ?_
    by_cases hmem : (0 : EuclideanSpace ℝ (Fin 0)) ∈ t
    · have huniv : t = Set.univ :=
        Set.eq_univ_of_forall (fun x => by
          rw [Subsingleton.elim x 0]
          exact hmem)
      rw [huniv, measure_univ, measure_univ]
    · have hempty : t = ∅ :=
        Set.eq_empty_of_forall_notMem (fun x hx => hmem (by
          rw [← Subsingleton.elim x 0]
          exact hx))
      rw [hempty, measure_empty, measure_empty]
  rw [heq]
  exact tvDist_self q

/-- With step `0` and one step, the output law is the standard Gaussian. -/
theorem ddpmOutput_zero_one
    (s : ℕ → EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) :
    ddpmOutput 0 s 1 = stdGaussian (EuclideanSpace ℝ (Fin 1)) := by
  rw [ddpmOutput_one]
  unfold ddpmStep
  simp only [Real.exp_zero, mul_zero, sub_self, Real.sqrt_zero, one_smul, zero_smul,
    add_zero]
  rw [show (fun p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) => p.1) = Prod.fst
    from rfl, Measure.map_fst_prod, measure_univ, one_smul]

/-- With step `0` and one step, the output is at full total variation distance from `dirac 0`. -/
theorem tvDist_ddpmOutput_dirac
    (s : ℕ → EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) :
    tvDist (ddpmOutput 0 s 1) (Measure.dirac 0) = 2 := by
  have hsing : Measure.MutuallySingular (stdGaussian (EuclideanSpace ℝ (Fin 1)))
      (Measure.dirac 0) := by
    refine ⟨{0}, measurableSet_singleton 0, ?_, ?_⟩
    · rw [MetaMathlibExt.stdGaussian_eq_withDensity]
      exact measure_singleton 0
    · rw [Measure.dirac_apply' 0 (measurableSet_singleton 0).compl]
      exact Set.indicator_of_notMem (by simp) 1
  rw [ddpmOutput_zero_one s, tvDist_of_mutuallySingular hsing, probReal_univ, probReal_univ]
  norm_num

#print axioms ouMarginal_zero
#print axioms ouMarginal_stdGaussian
#print axioms ddpmLaw_zero
#print axioms ddpmLaw_succ
#print axioms ddpmOutput_one
#print axioms ddpmOutput_congr
#print axioms isProbabilityMeasure_ouMarginal
#print axioms isProbabilityMeasure_ddpmStep
#print axioms isProbabilityMeasure_ddpmLaw
#print axioms isProbabilityMeasure_ddpmOutput

end Cslib.MachineLearning.ScoreDiffusionTests

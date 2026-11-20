/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate















open MeasureTheory Matrix ProbabilityTheory Set WithLp
open scoped ENNReal InnerProductSpace NNReal

namespace StatMech.SLE






noncomputable def brownianCovVector (t : ℝ) : Lp ℝ 2 (volume : Measure ℝ) :=
  indicatorConstLp 2 (s := uIoc 0 t) measurableSet_uIoc
    (by
      simp only [uIoc]
      exact (measure_Ioc_lt_top (μ := (volume : Measure ℝ))).ne) 1



noncomputable def brownianCovariance (s t : ℝ) : ℝ :=
  ⟪brownianCovVector s, brownianCovVector t⟫_ℝ

theorem brownianCovariance_eq_volumeReal (s t : ℝ) :
    brownianCovariance s t =
      (volume : Measure ℝ).real (uIoc 0 s ∩ uIoc 0 t) := by
  simp [brownianCovariance, brownianCovVector,
    L2.real_inner_indicatorConstLp_one_indicatorConstLp_one]


theorem brownianCovariance_eq (s t : ℝ) :
    brownianCovariance s t = (|s| + |t| - |t - s|) / 2 := by
  rw [brownianCovariance_eq_volumeReal, uIoc, uIoc, Ioc_inter_Ioc,
    Real.volume_real_Ioc]
  rcases le_total 0 s with hs | hs <;>
    rcases le_total 0 t with ht | ht <;>
      rcases le_total s t with hst | hst
  all_goals simp [hs, ht, hst, abs_of_nonneg, abs_of_nonpos] <;> linarith

@[simp]
theorem brownianCovariance_self (t : ℝ) : brownianCovariance t t = |t| := by
  rw [brownianCovariance_eq_volumeReal, inter_self, Measure.real]
  simp [Real.volume_uIoc]

@[simp]
theorem brownianCovariance_zero_left (t : ℝ) : brownianCovariance 0 t = 0 := by
  rw [brownianCovariance_eq_volumeReal]
  simp

@[simp]
theorem brownianCovariance_zero_right (t : ℝ) : brownianCovariance t 0 = 0 := by
  rw [brownianCovariance_eq_volumeReal]
  simp

theorem brownianCovariance_symm (s t : ℝ) :
    brownianCovariance s t = brownianCovariance t s := by
  simp only [brownianCovariance, real_inner_comm]


noncomputable def brownianCovarianceMatrix (I : Finset ℝ) : Matrix I I ℝ :=
  fun s t => brownianCovariance s t

theorem brownianCovarianceMatrix_eq_gram (I : Finset ℝ) :
    brownianCovarianceMatrix I = gram ℝ (fun t : I => brownianCovVector t) := rfl

theorem brownianCovarianceMatrix_posSemidef (I : Finset ℝ) :
    (brownianCovarianceMatrix I).PosSemidef := by
  rw [brownianCovarianceMatrix_eq_gram]
  exact Matrix.posSemidef_gram ℝ _


noncomputable def brownianFiniteDimensionalLaw (I : Finset ℝ) :
    Measure (EuclideanSpace ℝ I) :=
  ProbabilityTheory.multivariateGaussian 0 (brownianCovarianceMatrix I)

instance brownianFiniteDimensionalLaw.isProbabilityMeasure (I : Finset ℝ) :
    IsProbabilityMeasure (brownianFiniteDimensionalLaw I) := by
  unfold brownianFiniteDimensionalLaw
  infer_instance

instance brownianFiniteDimensionalLaw.isGaussian (I : Finset ℝ) :
    IsGaussian (brownianFiniteDimensionalLaw I) := by
  unfold brownianFiniteDimensionalLaw
  infer_instance

theorem memLp_eval_brownianFiniteDimensionalLaw
    (I : Finset ℝ) (t : I) :
    MemLp (fun x : EuclideanSpace ℝ I => x t) 2
      (brownianFiniteDimensionalLaw I) := by
  simpa only [EuclideanSpace.coe_proj] using
    (IsGaussian.memLp_dual (brownianFiniteDimensionalLaw I)
      (EuclideanSpace.proj t) 2 (by simp))



theorem brownianFiniteDimensionalLaw_measurePreserving_eval
    (I : Finset ℝ) (t : I) :
    MeasurePreserving (fun x : EuclideanSpace ℝ I => x t)
      (brownianFiniteDimensionalLaw I)
      (ProbabilityTheory.gaussianReal 0 |(t : ℝ)|.toNNReal) := by
  simpa [brownianFiniteDimensionalLaw, brownianCovarianceMatrix] using
    (ProbabilityTheory.measurePreserving_eval_multivariateGaussian
      (brownianCovarianceMatrix_posSemidef I) (μ := (0 : EuclideanSpace ℝ I))
      (i := t))

theorem integral_increment_brownianFiniteDimensionalLaw
    (I : Finset ℝ) (s t : I) :
    ∫ x, (x t - x s) ∂(brownianFiniteDimensionalLaw I) = 0 := by
  let L : EuclideanSpace ℝ I →L[ℝ] ℝ := EuclideanSpace.proj t - EuclideanSpace.proj s
  change ∫ x, L x ∂(brownianFiniteDimensionalLaw I) = 0
  rw [L.integral_comp_id_comm IsGaussian.integrable_id]
  simp [brownianFiniteDimensionalLaw]

theorem variance_increment_brownianFiniteDimensionalLaw
    (I : Finset ℝ) (s t : I) :
    Var[(fun x : EuclideanSpace ℝ I => x t - x s);
      brownianFiniteDimensionalLaw I] = |(t : ℝ) - (s : ℝ)| := by
  have ht : MemLp (fun x : EuclideanSpace ℝ I => x t) 2
      (brownianFiniteDimensionalLaw I) :=
    memLp_eval_brownianFiniteDimensionalLaw I t
  have hs : MemLp (fun x : EuclideanSpace ℝ I => x s) 2
      (brownianFiniteDimensionalLaw I) :=
    memLp_eval_brownianFiniteDimensionalLaw I s
  rw [variance_fun_sub ht hs]
  simp_rw [brownianFiniteDimensionalLaw,
    ProbabilityTheory.variance_eval_multivariateGaussian
      (brownianCovarianceMatrix_posSemidef I),
    ProbabilityTheory.covariance_eval_multivariateGaussian
      (brownianCovarianceMatrix_posSemidef I),
    brownianCovarianceMatrix, brownianCovariance_self, brownianCovariance_eq]
  rw [abs_sub_comm]
  ring



theorem brownianFiniteDimensionalLaw_measurePreserving_increment
    (I : Finset ℝ) (s t : I) :
    MeasurePreserving (fun x : EuclideanSpace ℝ I => x t - x s)
      (brownianFiniteDimensionalLaw I)
      (ProbabilityTheory.gaussianReal 0 |(t : ℝ) - (s : ℝ)|.toNNReal) where
  measurable := by fun_prop
  map_eq := by
    let L : EuclideanSpace ℝ I →L[ℝ] ℝ := EuclideanSpace.proj t - EuclideanSpace.proj s
    change (brownianFiniteDimensionalLaw I).map L = _
    rw [IsGaussian.map_eq_gaussianReal]
    congr 2
    · exact integral_increment_brownianFiniteDimensionalLaw I s t
    · exact variance_increment_brownianFiniteDimensionalLaw I s t

theorem covariance_disjoint_increments_brownianFiniteDimensionalLaw
    (I : Finset ℝ) (s t u v : I)
    (hst : (s : ℝ) ≤ t) (htu : (t : ℝ) ≤ u) (huv : (u : ℝ) ≤ v) :
    cov[(fun x : EuclideanSpace ℝ I => x t - x s),
      (fun x : EuclideanSpace ℝ I => x v - x u);
      brownianFiniteDimensionalLaw I] = 0 := by
  have hs := memLp_eval_brownianFiniteDimensionalLaw I s
  have ht := memLp_eval_brownianFiniteDimensionalLaw I t
  have hu := memLp_eval_brownianFiniteDimensionalLaw I u
  have hv := memLp_eval_brownianFiniteDimensionalLaw I v
  have hvu : MemLp (fun x : EuclideanSpace ℝ I => x v - x u) 2
      (brownianFiniteDimensionalLaw I) := by
    simpa only [Pi.sub_apply] using hv.sub hu
  rw [covariance_fun_sub_left ht hs hvu,
    covariance_fun_sub_right ht hv hu,
    covariance_fun_sub_right hs hv hu]
  simp_rw [brownianFiniteDimensionalLaw,
    ProbabilityTheory.covariance_eval_multivariateGaussian
      (brownianCovarianceMatrix_posSemidef I),
    brownianCovarianceMatrix, brownianCovariance_eq]
  have hsv : (s : ℝ) ≤ v := hst.trans (htu.trans huv)
  have hsu : (s : ℝ) ≤ u := hst.trans htu
  have htv : (t : ℝ) ≤ v := htu.trans huv
  simp [abs_of_nonneg (sub_nonneg.mpr htv),
    abs_of_nonneg (sub_nonneg.mpr htu),
    abs_of_nonneg (sub_nonneg.mpr hsv),
    abs_of_nonneg (sub_nonneg.mpr hsu)]
  ring



theorem brownianFiniteDimensionalLaw_indepFun_increments
    (I : Finset ℝ) (s t u v : I)
    (hst : (s : ℝ) ≤ t) (htu : (t : ℝ) ≤ u) (huv : (u : ℝ) ≤ v) :
    IndepFun (fun x : EuclideanSpace ℝ I => x t - x s)
      (fun x : EuclideanSpace ℝ I => x v - x u)
      (brownianFiniteDimensionalLaw I) := by
  let L₁ : EuclideanSpace ℝ I →L[ℝ] ℝ := EuclideanSpace.proj t - EuclideanSpace.proj s
  let L₂ : EuclideanSpace ℝ I →L[ℝ] ℝ := EuclideanSpace.proj v - EuclideanSpace.proj u
  have hpair : HasGaussianLaw (fun x : EuclideanSpace ℝ I =>
      (x t - x s, x v - x u)) (brownianFiniteDimensionalLaw I) := by
    have hL : HasGaussianLaw (L₁.prod L₂) (brownianFiniteDimensionalLaw I) :=
      IsGaussian.hasGaussianLaw
    simpa [L₁, L₂] using hL
  exact hpair.indepFun_of_covariance_eq_zero
    (covariance_disjoint_increments_brownianFiniteDimensionalLaw I s t u v hst htu huv)



theorem brownianFiniteDimensionalLaw_restrict
    {I J : Finset ℝ} (hJI : J ⊆ I) :
    MeasurePreserving (EuclideanSpace.restrict₂ hJI)
      (brownianFiniteDimensionalLaw I) (brownianFiniteDimensionalLaw J) := by
  simpa [brownianFiniteDimensionalLaw, brownianCovarianceMatrix] using
    (ProbabilityTheory.measurePreserving_restrict₂_multivariateGaussian
      (brownianCovarianceMatrix_posSemidef I) hJI
      (μ := (0 : EuclideanSpace ℝ I)))



noncomputable def brownianFiniteDimensionalPiLaw (I : Finset ℝ) :
    Measure (I → ℝ) :=
  (brownianFiniteDimensionalLaw I).map (WithLp.ofLp : EuclideanSpace ℝ I → (I → ℝ))

instance brownianFiniteDimensionalPiLaw.isProbabilityMeasure (I : Finset ℝ) :
    IsProbabilityMeasure (brownianFiniteDimensionalPiLaw I) := by
  unfold brownianFiniteDimensionalPiLaw
  exact Measure.isProbabilityMeasure_map
    (Measurable.aemeasurable (WithLp.measurable_ofLp 2 (I → ℝ)))



theorem brownianFiniteDimensionalPiLaw_isProjective :
    @IsProjectiveMeasureFamily ℝ (fun _ => ℝ) (fun _ => inferInstance)
      brownianFiniteDimensionalPiLaw := by
  intro I J hJI
  let fI : EuclideanSpace ℝ I → (I → ℝ) := @WithLp.ofLp 2 (I → ℝ)
  let fJ : EuclideanSpace ℝ J → (J → ℝ) := @WithLp.ofLp 2 (J → ℝ)
  let eRestrict : EuclideanSpace ℝ I → EuclideanSpace ℝ J :=
    EuclideanSpace.restrict₂ hJI
  let restrict : (I → ℝ) → (J → ℝ) :=
    Finset.restrict₂ (π := fun _ : ℝ => ℝ) hJI
  rw [brownianFiniteDimensionalPiLaw, brownianFiniteDimensionalPiLaw,
    ← (brownianFiniteDimensionalLaw_restrict hJI).map_eq]
  change ((brownianFiniteDimensionalLaw I).map eRestrict).map fJ =
    ((brownianFiniteDimensionalLaw I).map fI).map restrict
  have hfI : Measurable fI := WithLp.measurable_ofLp 2 (I → ℝ)
  have hfJ : Measurable fJ := WithLp.measurable_ofLp 2 (J → ℝ)
  have heRestrict : Measurable eRestrict :=
    (brownianFiniteDimensionalLaw_restrict hJI).measurable
  have hrestrict : Measurable restrict := Finset.measurable_restrict₂ hJI
  rw [Measure.map_map hfJ heRestrict, Measure.map_map hrestrict hfI]
  apply Measure.map_congr
  filter_upwards [] with x
  rfl

end StatMech.SLE

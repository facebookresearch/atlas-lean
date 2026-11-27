/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.LinearGaussianAllLawConverse

@[expose] public section

open MathlibExt.InformationTheory.LinearGaussianAllLawConverse
  MathlibExt.InformationTheory.LinearGaussianJointLaw MeasureTheory ProbabilityTheory
  InformationTheory Matrix WithLp
open scoped ENNReal

namespace MathlibExtTest.InformationTheory.LinearGaussianAllLawConverse

/-- A deterministic input at an arbitrary, possibly nonzero, point carries no information, here
through a nonsquare `2 × 3` channel: the bound at `K = 0` is `0`. -/
example (c : EuclideanSpace ℝ (Fin 3)) :
    measureMutualInformation
        (⟨Measure.dirac c ⊗ₘ
          MetaMathlibExt.noiseKernel
            (toEuclideanLin (!![1, 2, 3; 4, 5, 6] : Matrix (Fin 2) (Fin 3) ℝ))
            (MetaMathlibExt.continuous_toEuclideanLin _).measurable
            (multivariateGaussian 0 (1 : Matrix (Fin 2) (Fin 2) ℝ)),
          inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 2))) = 0 := by
  refine le_antisymm ?_ bot_le
  simpa using measureMutualInformation_dirac_compProd_noiseKernel_le
    (!![1, 2, 3; 4, 5, 6] : Matrix (Fin 2) (Fin 3) ℝ) PosDef.one c

/-- The two-point mixture is a probability measure, so the two-point bound below is not
vacuous. -/
example (x y : EuclideanSpace ℝ (Fin 1)) :
    IsProbabilityMeasure ((1 / 2 : ℝ≥0∞) • Measure.dirac x + (1 / 2 : ℝ≥0∞) • Measure.dirac y) := by
  constructor
  simp
  exact ENNReal.inv_two_add_inv_two

/-- The non-Gaussian two-point input `(δ (c + 1) + δ (c - 1)) / 2`, with an arbitrary mean `c`,
through `H = R = 1` on one coordinate: the bound is `1 / 2` bit. -/
example (c : EuclideanSpace ℝ (Fin 1)) (ρ : Measure (EuclideanSpace ℝ (Fin 1)))
    [IsProbabilityMeasure ρ]
    (hρ : ρ = (1 / 2 : ℝ≥0∞) • Measure.dirac (c + toLp 2 ![1]) +
      (1 / 2 : ℝ≥0∞) • Measure.dirac (c - toLp 2 ![1])) :
    measureMutualInformation
        (⟨ρ ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ))
            (MetaMathlibExt.continuous_toEuclideanLin _).measurable
            (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ)),
          inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) ≤
      ENNReal.ofReal (1 / 2) := by
  have h := measureMutualInformation_twoPoint_compProd_noiseKernel_le
    (1 : Matrix (Fin 1) (Fin 1) ℝ) PosDef.one c (toLp 2 ![1]) ρ hρ
  have hv : Real.log (((1 : Matrix (Fin 1) (Fin 1) ℝ) +
      1 * vecMulVec (ofLp (toLp 2 ![(1 : ℝ)])) (ofLp (toLp 2 ![1])) *
        (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ).det / (1 : Matrix (Fin 1) (Fin 1) ℝ).det) /
      (2 * Real.log 2) = 1 / 2 := by
    have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    rw [Matrix.det_one, div_one, Matrix.det_fin_one]
    simp
    norm_num
    field_simp
  rwa [hv] at h

/-- The headline applies to a nonzero-mean input: on `δ c × N(0, 1)`, the first coordinate is
the input and the second the independent noise; its covariance is positive semidefinite, has
trace at most `‖c‖²`, and bounds the mutual information. -/
example (H : Matrix (Fin 2) (Fin 2) ℝ) (c : EuclideanSpace ℝ (Fin 2)) :
    let μ := (Measure.dirac c).prod
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (1 : Matrix (Fin 2) (Fin 2) ℝ))
    let K : Matrix (Fin 2) (Fin 2) ℝ := fun a b =>
      cov[fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => p.1 a,
        fun p => p.1 b; μ]
    K.PosSemidef ∧ K.trace ≤ ‖c‖ ^ 2 ∧
      measureMutualInformation
          (⟨μ.map (fun p => (p.1, toEuclideanLin H p.1 + p.2)), inferInstance⟩ :
            ProbabilityMeasure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) ≤
        ENNReal.ofReal
          (Real.log ((1 + H * K * Hᵀ).det / (1 : Matrix (Fin 2) (Fin 2) ℝ).det) /
            (2 * Real.log 2)) := by
  intro μ K
  have hind : IndepFun (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => p.1)
      (fun p => p.2) μ :=
    indepFun_prod (X := fun x : EuclideanSpace ℝ (Fin 2) => x)
      (Y := fun y : EuclideanSpace ℝ (Fin 2) => y) measurable_id measurable_id
  have hlaw : μ.map Prod.snd = multivariateGaussian 0 (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    simp [μ]
  have hpow : PowerConstraint μ (fun p => p.1) (‖c‖ ^ 2) := by
    refine ⟨by positivity, ?_⟩
    have hf : Measurable fun x : EuclideanSpace ℝ (Fin 2) => ENNReal.ofReal (‖x‖ ^ 2) :=
      ((continuous_norm.pow 2).measurable).ennreal_ofReal
    rw [← lintegral_map hf measurable_fst, Measure.map_fst_prod]
    simp
  exact measureMutualInformation_linearGaussianChannel_le H PosDef.one measurable_fst
    measurable_snd hind hlaw hpow (fun a b => rfl)

/-- Without positive definite noise the bound fails: the noiseless channel `Y = X` with
`X ~ N(0, 1)` has infinite mutual information while the expression evaluates to `0`. -/
example :
    ¬ measureMutualInformation
        (⟨multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₘ
          MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ))
            (MetaMathlibExt.continuous_toEuclideanLin _).measurable
            (multivariateGaussian 0 (0 : Matrix (Fin 1) (Fin 1) ℝ)),
          inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) ≤
      ENNReal.ofReal (Real.log (((0 : Matrix (Fin 1) (Fin 1) ℝ) +
          1 * (1 : Matrix (Fin 1) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ).det /
          (0 : Matrix (Fin 1) (Fin 1) ℝ).det) / (2 * Real.log 2)) :=
  not_measureMutualInformation_noiseless_le

/-- With unit noise instead, the same deterministic-input check gives `0`: the noise must be
positive definite for the bound, not merely present. -/
example (c : EuclideanSpace ℝ (Fin 1)) :
    measureMutualInformation
        (⟨Measure.dirac c ⊗ₘ
          MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ))
            (MetaMathlibExt.continuous_toEuclideanLin _).measurable
            (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ)),
          inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) = 0 := by
  refine le_antisymm ?_ bot_le
  simpa using measureMutualInformation_dirac_compProd_noiseKernel_le
    (1 : Matrix (Fin 1) (Fin 1) ℝ) PosDef.one c

end MathlibExtTest.InformationTheory.LinearGaussianAllLawConverse

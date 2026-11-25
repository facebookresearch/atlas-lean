/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.GaussianChannelLogDet

@[expose] public section

open MathlibExt.InformationTheory.GaussianChannelLogDet MeasureTheory ProbabilityTheory
  InformationTheory Matrix

namespace MathlibExtTest.InformationTheory.GaussianChannelLogDet

/-- A zero input covariance carries no information, here through a nonsquare `2 × 3` channel. -/
example :
    measureMutualInformation
        (⟨multivariateGaussian 0 (0 : Matrix (Fin 3) (Fin 3) ℝ) ⊗ₘ
          MetaMathlibExt.noiseKernel
            (toEuclideanLin (!![1, 2, 3; 4, 5, 6] : Matrix (Fin 2) (Fin 3) ℝ))
            (MetaMathlibExt.continuous_toEuclideanLin _).measurable
            (multivariateGaussian 0 (1 : Matrix (Fin 2) (Fin 2) ℝ)),
          inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 2))) = 0 :=
  measureMutualInformation_gaussianInput_zero _ PosDef.one

/-- The general formula agrees at `K = 0`: the log-determinant ratio is `log 1 = 0`. -/
example :
    measureMutualInformation
        (⟨multivariateGaussian 0 (0 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₘ
          MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 2) (Fin 2) ℝ))
            (MetaMathlibExt.continuous_toEuclideanLin _).measurable
            (multivariateGaussian 0 (1 : Matrix (Fin 2) (Fin 2) ℝ)),
          inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) = 0 := by
  rw [measureMutualInformation_gaussianInput_compProd_noiseKernel _ PosSemidef.zero PosDef.one]
  simp

/-- The full-rank nondiagonal covariance `[[2, 1], [1, 2]]` with `H = R = 1` gives `3 / 2`
bits. -/
example :
    measureMutualInformation
        (⟨multivariateGaussian 0 (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₘ
          MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 2) (Fin 2) ℝ))
            (MetaMathlibExt.continuous_toEuclideanLin _).measurable
            (multivariateGaussian 0 (1 : Matrix (Fin 2) (Fin 2) ℝ)),
          inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) =
      ENNReal.ofReal (3 / 2) :=
  measureMutualInformation_gaussianInput_nondiagonal

/-- The rank-one covariance `v vᵀ` with `v = (1, 2)` is singular. -/
example : (vecMulVec ![(1 : ℝ), 2] ![1, 2]).det = 0 := by
  simp [det_fin_two]

/-- Singular rank-one input `v = (1, 2)` through `H = R = 1`: `1 + vᵀ v = 6`, so the mutual
information is `log 6 / (2 log 2)` bits. -/
example :
    measureMutualInformation
        (⟨multivariateGaussian 0 (vecMulVec ![(1 : ℝ), 2] ![1, 2]) ⊗ₘ
          MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 2) (Fin 2) ℝ))
            (MetaMathlibExt.continuous_toEuclideanLin _).measurable
            (multivariateGaussian 0 (1 : Matrix (Fin 2) (Fin 2) ℝ)),
          inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) =
      ENNReal.ofReal (Real.log 6 / (2 * Real.log 2)) := by
  rw [measureMutualInformation_gaussianInput_rankOne _ _ PosDef.one]
  congr 3
  simp [dotProduct, Fin.sum_univ_two]
  norm_num

/-- The scalar case with gain `1`, input variance `3` and noise variance `1` gives
`log 4 / (2 log 2) = 1` bit. -/
example :
    measureMutualInformation
        (⟨multivariateGaussian 0 (!![3] : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₘ
          MetaMathlibExt.noiseKernel (toEuclideanLin (!![1] : Matrix (Fin 1) (Fin 1) ℝ))
            (MetaMathlibExt.continuous_toEuclideanLin _).measurable
            (multivariateGaussian 0 (!![1] : Matrix (Fin 1) (Fin 1) ℝ)),
          inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) =
      ENNReal.ofReal 1 := by
  rw [measureMutualInformation_gaussianInput_fin_one 1 3 1 (by norm_num) one_pos]
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  congr 1
  norm_num [h4]

/-- The random-variable hypotheses are jointly satisfiable: on `N(0, K) × N(0, R)` the
coordinates are independent with the required laws, for every positive semidefinite `K`. -/
example {K : Matrix (Fin 2) (Fin 2) ℝ} (hK : K.PosSemidef) :
    measureMutualInformation
        (⟨((multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) K).prod
            (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) 1)).map
            (fun ω => (ω.1, toEuclideanLin (1 : Matrix (Fin 2) (Fin 2) ℝ) ω.1 + ω.2)),
          inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) =
      ENNReal.ofReal (Real.log ((1 + 1 * K * 1ᵀ).det / (1 : Matrix (Fin 2) (Fin 2) ℝ).det) /
        (2 * Real.log 2)) :=
  measureMutualInformation_linearGaussianChannel_gaussianInput 1 hK PosDef.one measurable_fst
    measurable_snd
    ((indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
      measurable_snd.aemeasurable).2 (by simp))
    (by simp) (by simp)

/-- The output law needs only positive semidefinite noise: with singular noise `R = 0` and
`H = 1`, the output of `N(0, K)` is `N(0, K)`. -/
example {K : Matrix (Fin 2) (Fin 2) ℝ} (hK : K.PosSemidef) :
    (multivariateGaussian 0 K ⊗ₘ
        MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 2) (Fin 2) ℝ))
          (MetaMathlibExt.continuous_toEuclideanLin _).measurable
          (multivariateGaussian 0 (0 : Matrix (Fin 2) (Fin 2) ℝ))).map Prod.snd =
      multivariateGaussian 0 K := by
  rw [map_snd_gaussianInput_compProd_noiseKernel _ hK PosSemidef.zero]
  simp

/-- Positive definite noise is needed: the noiseless channel has infinite mutual information. -/
example :
    measureMutualInformation
        (⟨multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₘ
          MetaMathlibExt.noiseKernel (toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ))
            (MetaMathlibExt.continuous_toEuclideanLin _).measurable
            (multivariateGaussian 0 (0 : Matrix (Fin 1) (Fin 1) ℝ)),
          inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) = ⊤ :=
  measureMutualInformation_noiseless_ne_logDet.1

end MathlibExtTest.InformationTheory.GaussianChannelLogDet

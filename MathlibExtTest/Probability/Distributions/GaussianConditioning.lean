/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Distributions.GaussianConditioning

open MetaMathlibExt MeasureTheory ProbabilityTheory Matrix

-- Conditioning a two-dimensional block on a one-dimensional block of a Gaussian vector.
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Ω → EuclideanSpace ℝ (Fin 2 ⊕ Fin 1)} (hV : Measurable V)
    {μ : EuclideanSpace ℝ (Fin 2 ⊕ Fin 1)} {S : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ}
    (hS : S.PosSemidef) (hlaw : P.map V = multivariateGaussian μ S)
    (hYY : IsUnit S.toBlocks₂₂.det) :
    ∀ᵐ y ∂P.map (fun ω => toEuclideanLin (blockRow (0 : Matrix (Fin 1) (Fin 2) ℝ) 1) (V ω)),
      condDistrib (fun ω => toEuclideanLin (blockRow (1 : Matrix (Fin 2) (Fin 2) ℝ) 0) (V ω))
          (fun ω => toEuclideanLin (blockRow (0 : Matrix (Fin 1) (Fin 2) ℝ) 1) (V ω)) P y =
        multivariateGaussian
          (toEuclideanLin (blockRow (1 : Matrix (Fin 2) (Fin 2) ℝ) 0) μ +
            toEuclideanLin (S.toBlocks₁₂ * S.toBlocks₂₂⁻¹)
              (y - toEuclideanLin (blockRow (0 : Matrix (Fin 1) (Fin 2) ℝ) 1) μ))
          (S.toBlocks₁₁ - S.toBlocks₁₂ * S.toBlocks₂₂⁻¹ * S.toBlocks₂₁) :=
  condDistrib_multivariateGaussian hV hS hlaw hYY

-- A signal observed in independent Gaussian noise.
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → EuclideanSpace ℝ (Fin 3)} {Z : Ω → EuclideanSpace ℝ (Fin 2)} (hY : Measurable Y)
    (hZ : Measurable Z) (hind : IndepFun Y Z P) (H : Matrix (Fin 2) (Fin 3) ℝ) :
    condDistrib (fun ω => toEuclideanLin H (Y ω) + Z ω) Y P =ᵐ[P.map Y]
      noiseKernel (toEuclideanLin H) (continuous_toEuclideanLin H).measurable (P.map Z) :=
  condDistrib_add_of_indepFun hY hZ hind _

-- Linear images: `M · N(μ, S) = N(M μ, M S Mᵀ)`.
example (M : Matrix (Fin 2) (Fin 3) ℝ) (μ : EuclideanSpace ℝ (Fin 3))
    (S : Matrix (Fin 3) (Fin 3) ℝ) (hS : S.PosSemidef) :
    (multivariateGaussian μ S).map (toEuclideanLin M) =
      multivariateGaussian (toEuclideanLin M μ) (M * S * Mᵀ) :=
  map_toEuclideanLin_multivariateGaussian M μ hS

section Blocks

open WithLp

-- Concatenation puts the two blocks side by side.
example : (EuclideanSpace.sumEquivProd (𝕜 := ℝ)).symm ((toLp 2 ![1, 2] : EuclideanSpace ℝ (Fin 2)),
    (toLp 2 ![3] : EuclideanSpace ℝ (Fin 1))) (Sum.inr 0) = 3 := by
  simp

example : (EuclideanSpace.sumEquivProd (𝕜 := ℝ)).symm ((toLp 2 ![1, 2] : EuclideanSpace ℝ (Fin 2)),
    (toLp 2 ![3] : EuclideanSpace ℝ (Fin 1))) (Sum.inl 1) = 2 := by
  simp

-- Independent Gaussian state and noise concatenate to a block-diagonal Gaussian.
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {x : Ω → EuclideanSpace ℝ (Fin 2)} {v : Ω → EuclideanSpace ℝ (Fin 1)} (hx : Measurable x)
    (hv : Measurable v) (hind : IndepFun x v P) {m : EuclideanSpace ℝ (Fin 2)}
    {S : Matrix (Fin 2) (Fin 2) ℝ} {R : Matrix (Fin 1) (Fin 1) ℝ} (hS : S.PosSemidef)
    (hR : R.PosSemidef) (hxl : P.map x = multivariateGaussian m S)
    (hvl : P.map v = multivariateGaussian 0 R) :
    P.map (fun ω => (EuclideanSpace.sumEquivProd (𝕜 := ℝ)).symm (x ω, v ω)) =
      multivariateGaussian ((EuclideanSpace.sumEquivProd (𝕜 := ℝ)).symm (m, 0))
        (fromBlocks S 0 0 R) :=
  map_sumEquivProd_symm_of_indepFun hx hv hind hS hR hxl hvl

-- The block-diagonal covariance of two identities is positive semidefinite.
example :
    (fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosSemidef :=
  posSemidef_fromBlocks_zero PosSemidef.one PosSemidef.one


end Blocks

section LinearModel

open WithLp

-- The marginal of a linear-Gaussian model with a `1 × 2` map.
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {x : Ω → EuclideanSpace ℝ (Fin 2)} {w : Ω → EuclideanSpace ℝ (Fin 1)} (hx : Measurable x)
    (hw : Measurable w) (hind : IndepFun x w P) {m : EuclideanSpace ℝ (Fin 2)}
    {S : Matrix (Fin 2) (Fin 2) ℝ} {Q : Matrix (Fin 1) (Fin 1) ℝ} (hS : S.PosSemidef)
    (hQ : Q.PosSemidef) (hxl : P.map x = multivariateGaussian m S)
    (hwl : P.map w = multivariateGaussian 0 Q) (F : Matrix (Fin 1) (Fin 2) ℝ) :
    P.map (fun ω => toEuclideanLin F (x ω) + w ω) =
      multivariateGaussian (toEuclideanLin F m + 0) (F * S * Fᵀ + Q) :=
  map_linear_add_of_indepFun hx hw hind hS hQ hxl hwl F

-- Bayes' theorem for a two-dimensional state observed through a `1 × 2` map.
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {x : Ω → EuclideanSpace ℝ (Fin 2)} {v : Ω → EuclideanSpace ℝ (Fin 1)} (hx : Measurable x)
    (hv : Measurable v) (hind : IndepFun x v P) {m : EuclideanSpace ℝ (Fin 2)}
    {S : Matrix (Fin 2) (Fin 2) ℝ} {R : Matrix (Fin 1) (Fin 1) ℝ} (hS : S.PosSemidef)
    (hR : R.PosSemidef) (hxl : P.map x = multivariateGaussian m S)
    (hvl : P.map v = multivariateGaussian 0 R) (H : Matrix (Fin 1) (Fin 2) ℝ)
    (hinv : IsUnit (H * S * Hᵀ + R).det) :
    ∀ᵐ y ∂P.map (fun ω => toEuclideanLin H (x ω) + v ω),
      condDistrib x (fun ω => toEuclideanLin H (x ω) + v ω) P y =
        multivariateGaussian
          (m + toEuclideanLin (S * Hᵀ * (H * S * Hᵀ + R)⁻¹) (y - toEuclideanLin H m))
          (S - S * Hᵀ * (H * S * Hᵀ + R)⁻¹ * (H * S)) :=
  condDistrib_linear_add_of_indepFun hx hv hind hS hR hxl hvl H hinv

-- `[A B] (a, b) = A a + B b`.
example (A : Matrix (Fin 1) (Fin 2) ℝ) (B : Matrix (Fin 1) (Fin 1) ℝ)
    (a : EuclideanSpace ℝ (Fin 2)) (b : EuclideanSpace ℝ (Fin 1)) :
    toEuclideanLin (blockRow A B) ((EuclideanSpace.sumEquivProd (𝕜 := ℝ)).symm (a, b)) =
      toEuclideanLin A a + toEuclideanLin B b :=
  toEuclideanLin_blockRow_sumEquivProd_symm A B a b

-- The posterior covariance is positive semidefinite.
example {S : Matrix (Fin 2) (Fin 2) ℝ} {R : Matrix (Fin 1) (Fin 1) ℝ} (hS : S.PosSemidef)
    (hR : R.PosDef) (H : Matrix (Fin 1) (Fin 2) ℝ) :
    (S - S * Hᵀ * (H * S * Hᵀ + R)⁻¹ * (H * S)).PosSemidef :=
  posSemidef_sub_mul_inv_mul hS hR H

end LinearModel

#print axioms condDistrib_multivariateGaussian
#print axioms condDistrib_add_of_indepFun
#print axioms map_sumEquivProd_symm_of_indepFun
#print axioms condDistrib_linear_add_of_indepFun

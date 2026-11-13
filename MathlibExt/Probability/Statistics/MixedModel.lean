/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.MixedModel
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Kernel.CondDistrib

import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Mixed-model response laws

Marginal and conditional laws of `Y = X β + Z γ + ε` with independent
centered Gaussian random effects `γ` and residual `ε`.

The marginal law is Gaussian with mean `X β` and covariance `Z G Zᵀ + R`.
The conditional law given `γ = g` is Gaussian with mean `X β + Z g` and
covariance `R`. Mean and covariance formulas follow from the Gaussian laws.

For the reverse conditional law (random effects given the response), see
`MathlibExt.Biology.StatisticalGenetics.MixedModel.condDistrib_mixedModel`.
-/

open MeasureTheory ProbabilityTheory Matrix MetaMathlibExt
open MathlibExt.Biology.StatisticalGenetics.MixedModel (phenCov)

namespace MathlibExt.Probability.Statistics.MixedModel

@[expose] public section

/-- Marginal law of the mixed-model response: with `γ ~ N(0, G)` and
`ε ~ N(0, R)` independent, `Y = X β + Z γ + ε` is
`N(X β, Z G Zᵀ + R)`. -/
theorem map_mixedModel_response {n p q : Type*} [Fintype n] [DecidableEq n]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ q) (ε : Ω → EuclideanSpace ℝ n)
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix n p ℝ) (β : EuclideanSpace ℝ p) (Z : Matrix n q ℝ)
    (G : Matrix q q ℝ) (R : Matrix n n ℝ)
    (hG : G.PosSemidef) (hR : R.PosSemidef)
    (hγl : P.map γ = multivariateGaussian 0 G)
    (hεl : P.map ε = multivariateGaussian 0 R) :
    P.map (fun ω => toEuclideanLin X β + toEuclideanLin Z (γ ω) + ε ω) =
      multivariateGaussian (toEuclideanLin X β) (phenCov Z G R) := by
  have hsum : P.map (fun ω => toEuclideanLin Z (γ ω) + ε ω) =
      multivariateGaussian 0 (Z * G * Zᵀ + R) := by
    simpa using map_linear_add_of_indepFun hγ hε hind hG hR hγl hεl Z
  have hshift : P.map (fun ω => toEuclideanLin X β + toEuclideanLin Z (γ ω) +
      ε ω) = P.map (fun ω => toEuclideanLin X β +
      (toEuclideanLin Z (γ ω) + ε ω)) := by
    congr 1
    funext ω
    abel
  have hfg : Measurable (fun ω => toEuclideanLin Z (γ ω) + ε ω) :=
    ((continuous_toEuclideanLin Z).measurable.comp hγ).add hε
  have hf : Measurable (fun v : EuclideanSpace ℝ n => toEuclideanLin X β + v) :=
    measurable_const_add _
  have hconst : P.map (fun ω : Ω => toEuclideanLin X β +
      (toEuclideanLin Z (γ ω) + ε ω)) =
      (P.map (fun ω => toEuclideanLin Z (γ ω) + ε ω)).map
        (fun v => toEuclideanLin X β + v) :=
    (Measure.map_map hf hfg).symm
  rw [hshift, hconst, hsum]
  have hphen : (Z * G * Zᵀ + R) = phenCov Z G R := by
    simp [phenCov]
  rw [hphen, map_add_multivariateGaussian, add_zero]

/-- The marginal covariance `Z G Zᵀ + R` of the mixed model is positive
semidefinite. -/
theorem posSemidef_phenCov_of_posSemidef {n q : Type*} [Finite n]
    [Fintype q] (Z : Matrix n q ℝ) (G : Matrix q q ℝ)
    (R : Matrix n n ℝ) (hG : G.PosSemidef) (hR : R.PosSemidef) :
    (phenCov Z G R).PosSemidef := by
  have hZG : (Z * G * Zᵀ).PosSemidef := by
    have hEq : Z * G * Zᵀ = Z * G * Zᴴ := by
      simp [Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [hEq]
    exact hG.mul_mul_conjTranspose_same Z
  have hphen : phenCov Z G R = Z * G * Zᵀ + R := by
    simp [phenCov]
  rw [hphen]
  exact hZG.add hR

/-- Marginal mean of the mixed-model response: `E[Y] = X β`. -/
theorem integral_mixedModel_response {n p q : Type*} [Fintype n] [DecidableEq n]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ q) (ε : Ω → EuclideanSpace ℝ n)
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix n p ℝ) (β : EuclideanSpace ℝ p) (Z : Matrix n q ℝ)
    (G : Matrix q q ℝ) (R : Matrix n n ℝ)
    (hG : G.PosSemidef) (hR : R.PosDef)
    (hγl : P.map γ = multivariateGaussian 0 G)
    (hεl : P.map ε = multivariateGaussian 0 R) :
    ∫ ω, (toEuclideanLin X β + toEuclideanLin Z (γ ω) + ε ω) ∂P =
      toEuclideanLin X β := by
  have hYmeas : AEStronglyMeasurable
      (fun ω => toEuclideanLin X β + toEuclideanLin Z (γ ω) + ε ω) P := by
    fun_prop
  have hmap := map_mixedModel_response γ ε hγ hε hind X β Z G R hG
    hR.posSemidef hγl hεl
  have hpsd : (phenCov Z G R).PosSemidef :=
    posSemidef_phenCov_of_posSemidef Z G R hG hR.posSemidef
  calc ∫ ω, (toEuclideanLin X β + toEuclideanLin Z (γ ω) + ε ω) ∂P
      = ∫ y, y ∂(P.map
        (fun ω => toEuclideanLin X β + toEuclideanLin Z (γ ω) + ε ω)) :=
        (integral_map hYmeas.aemeasurable aestronglyMeasurable_id).symm
    _ = ∫ y, y ∂(multivariateGaussian (toEuclideanLin X β)
        (phenCov Z G R)) := by
        rw [hmap]
    _ = toEuclideanLin X β := integral_id_multivariateGaussian

/-- Marginal covariance of the mixed-model response: `Cov(Y) = Z G Zᵀ + R`. -/
theorem covariance_mixedModel_response {n p q : Type*} [Fintype n] [DecidableEq n]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ q) (ε : Ω → EuclideanSpace ℝ n)
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix n p ℝ) (β : EuclideanSpace ℝ p) (Z : Matrix n q ℝ)
    (G : Matrix q q ℝ) (R : Matrix n n ℝ)
    (hG : G.PosSemidef) (hR : R.PosDef)
    (hγl : P.map γ = multivariateGaussian 0 G)
    (hεl : P.map ε = multivariateGaussian 0 R) (i j : n) :
    cov[fun ω => (toEuclideanLin X β + toEuclideanLin Z (γ ω) + ε ω).ofLp i,
      fun ω => (toEuclideanLin X β + toEuclideanLin Z (γ ω) + ε ω).ofLp j;
      P] = phenCov Z G R i j := by
  have hmap := map_mixedModel_response γ ε hγ hε hind X β Z G R hG
    hR.posSemidef hγl hεl
  have hpsd : (phenCov Z G R).PosSemidef :=
    posSemidef_phenCov_of_posSemidef Z G R hG hR.posSemidef
  have hYmeas : AEStronglyMeasurable
      (fun ω => toEuclideanLin X β + toEuclideanLin Z (γ ω) + ε ω) P := by
    fun_prop
  have hci : Measurable (fun y : EuclideanSpace ℝ n => y.ofLp i) := by
    rw [← EuclideanSpace.coe_proj]
    exact (EuclideanSpace.proj i).continuous.measurable
  have hcj : Measurable (fun y : EuclideanSpace ℝ n => y.ofLp j) := by
    rw [← EuclideanSpace.coe_proj]
    exact (EuclideanSpace.proj j).continuous.measurable
  have hXi : AEStronglyMeasurable (fun y : EuclideanSpace ℝ n => y.ofLp i)
      (P.map (fun ω => toEuclideanLin X β + toEuclideanLin Z (γ ω) + ε ω)) :=
    hci.aestronglyMeasurable
  have hXj : AEStronglyMeasurable (fun y : EuclideanSpace ℝ n => y.ofLp j)
      (P.map (fun ω => toEuclideanLin X β + toEuclideanLin Z (γ ω) + ε ω)) :=
    hcj.aestronglyMeasurable
  have hcov : cov[fun ω => (toEuclideanLin X β + toEuclideanLin Z (γ ω) +
      ε ω).ofLp i,
      fun ω => (toEuclideanLin X β + toEuclideanLin Z (γ ω) + ε ω).ofLp j;
      P] = cov[fun y : EuclideanSpace ℝ n => y.ofLp i,
      fun y : EuclideanSpace ℝ n => y.ofLp j;
      P.map (fun ω => toEuclideanLin X β + toEuclideanLin Z (γ ω) + ε ω)] :=
    (covariance_map hXi hXj hYmeas.aemeasurable).symm
  rw [hcov, hmap]
  exact covariance_eval_multivariateGaussian hpsd i j

/-- Conditional law of the mixed-model response given the random effects:
`Y | γ = g ~ N(X β + Z g, R)`. -/
theorem condDistrib_mixedModel_response {n p q : Type*} [Fintype n]
    [DecidableEq n] [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ q) (ε : Ω → EuclideanSpace ℝ n)
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix n p ℝ) (β : EuclideanSpace ℝ p) (Z : Matrix n q ℝ)
    (R : Matrix n n ℝ)
    (hεl : P.map ε = multivariateGaussian 0 R) :
    ∀ᵐ g ∂P.map γ, condDistrib
        (fun ω => toEuclideanLin X β + toEuclideanLin Z (γ ω) + ε ω) γ P g =
        multivariateGaussian (toEuclideanLin X β + toEuclideanLin Z g) R := by
  have hfm : Measurable
      (fun g : EuclideanSpace ℝ q => toEuclideanLin X β + toEuclideanLin Z g) :=
    ((continuous_toEuclideanLin Z).measurable).const_add _
  have h : condDistrib
      (fun ω => toEuclideanLin X β + toEuclideanLin Z (γ ω) + ε ω) γ P
      =ᵐ[P.map γ] noiseKernel
        (fun g => toEuclideanLin X β + toEuclideanLin Z g) hfm (P.map ε) :=
    condDistrib_add_of_indepFun hγ hε hind hfm
  rw [hεl] at h
  filter_upwards [h] with g hg
  rw [hg]
  have h2 : noiseKernel (fun g => toEuclideanLin X β + toEuclideanLin Z g) hfm
      (multivariateGaussian (0 : EuclideanSpace ℝ n) R) g =
      (multivariateGaussian (0 : EuclideanSpace ℝ n) R).map
        ((toEuclideanLin X β + toEuclideanLin Z g) + ·) :=
    noiseKernel_apply _ _ _ _
  rw [h2, map_add_multivariateGaussian, add_zero]

/-- Conditional mean of the mixed-model response: `E[Y | γ] = X β + Z γ`. -/
theorem integral_condDistrib_mixedModel_response {n p q : Type*}
    [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p] [Fintype q]
    [DecidableEq q]
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ q) (ε : Ω → EuclideanSpace ℝ n)
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix n p ℝ) (β : EuclideanSpace ℝ p) (Z : Matrix n q ℝ)
    (R : Matrix n n ℝ)
    (hεl : P.map ε = multivariateGaussian 0 R) :
    ∀ᵐ g ∂P.map γ, ∫ y, y ∂(condDistrib
        (fun ω => toEuclideanLin X β + toEuclideanLin Z (γ ω) + ε ω) γ P g) =
        toEuclideanLin X β + toEuclideanLin Z g := by
  have hcond := condDistrib_mixedModel_response γ ε hγ hε hind X β Z R hεl
  filter_upwards [hcond] with g hg
  rw [hg]
  exact integral_id_multivariateGaussian

/-- Conditional covariance of the mixed-model response: `Cov(Y | γ) = R`. -/
theorem covariance_condDistrib_mixedModel_response {n p q : Type*}
    [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p] [Fintype q]
    [DecidableEq q]
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ q) (ε : Ω → EuclideanSpace ℝ n)
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix n p ℝ) (β : EuclideanSpace ℝ p) (Z : Matrix n q ℝ)
    (R : Matrix n n ℝ) (hR : R.PosDef)
    (hεl : P.map ε = multivariateGaussian 0 R) (i j : n) :
    ∀ᵐ g ∂P.map γ, cov[fun y : EuclideanSpace ℝ n => y.ofLp i,
      fun y : EuclideanSpace ℝ n => y.ofLp j;
      condDistrib (fun ω => toEuclideanLin X β + toEuclideanLin Z (γ ω) + ε ω)
        γ P g] = R i j := by
  have hcond := condDistrib_mixedModel_response γ ε hγ hε hind X β Z R hεl
  filter_upwards [hcond] with g hg
  rw [hg]
  exact covariance_eval_multivariateGaussian hR.posSemidef i j

end

end MathlibExt.Probability.Statistics.MixedModel

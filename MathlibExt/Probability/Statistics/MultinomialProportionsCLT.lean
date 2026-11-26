/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultivariateCLT

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Probability.Distributions.Gaussian.CharFun

/-! # Central limit theorem for multinomial proportions -/

open MeasureTheory Filter Finset Matrix
open scoped Real Topology

namespace ProbabilityTheory

private theorem oneHot_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    (EuclideanSpace.basisFun ι ℝ i) j = (if i = j then 1 else 0) := by
  simp [EuclideanSpace.basisFun_apply, PiLp.single_apply, eq_comm]

/-- **Central limit theorem for multinomial proportions.** For independent identically distributed
categorical draws with masses `p`, the associated one-hot vector has mean `p` and covariance
`C = diagonal p - p pᵀ`. The centered empirical proportions multiplied by `√n` converge in
distribution to `multivariateGaussian 0 C`. The covariance is positive semidefinite and singular:
it annihilates the all-ones vector. A zero-probability category has the point mass at zero as its
limiting coordinate law. No category mass is required to be strictly positive.

See J. Brunner, *Random Vectors Part Two*, slides 23–25, for the reduced-coordinate version. -/
public theorem multinomial_proportions_clt {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (Z : ℕ → Ω → ι) (p : ι → ℝ)
    (hpsum : ∑ i, p i = 1) (hprob : ∀ i, P.real {ω | Z 0 ω = i} = p i)
    (hindep : iIndepFun Z P) (hident : ∀ n, IdentDistrib (Z n) (Z 0) P P) :
    let X := fun n ω => EuclideanSpace.basisFun ι ℝ (Z n ω)
    let C := Matrix.diagonal p - Matrix.vecMulVec p p
    (∫ ω, X 0 ω ∂P) = WithLp.toLp 2 p ∧
      (∀ i j, cov[fun ω => (X 0 ω) i, fun ω => (X 0 ω) j; P] = C i j) ∧
      C.PosSemidef ∧ C *ᵥ 1 = 0 ∧ ¬IsUnit C ∧
      TendstoInDistribution
        (fun (n : ℕ) ω => √(n : ℝ) • ((n : ℝ)⁻¹ • ∑ k ∈ range n, X k ω - WithLp.toLp 2 p))
        atTop id (fun _ => P) (multivariateGaussian 0 C) ∧
      (∀ i, p i = 0 → (multivariateGaussian 0 C).map (fun x => x i) = Measure.dirac 0) := by
  intro X C
  have hhot : Measurable (EuclideanSpace.basisFun ι ℝ : ι → EuclideanSpace ℝ ι) :=
    Measurable.of_discrete
  have hidentX (n : ℕ) : IdentDistrib (X n) (X 0) P P := (hident n).comp hhot
  have hindepX : iIndepFun X P := hindep.comp _ (fun _ => hhot)
  have hcoord (i : ι) : (fun ω => (X 0 ω) i) =
      {ω | Z 0 ω = i}.indicator (1 : Ω → ℝ) := by
    funext ω
    by_cases hw : Z 0 ω = i
    · simp [X, hw]
    · simp [X, hw, Ne.symm hw]
  have hpLp (i : ι) : MemLp (fun ω => (X 0 ω) i) 2 P := by
    have hm : AEMeasurable (fun ω => (X 0 ω) i) P :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable.comp_aemeasurable
        (hidentX 0).aemeasurable_fst
    refine MemLp.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun ω => ?_)
    simp only [X, oneHot_apply]
    split <;> norm_num
  have hX : MemLp (X 0) 2 P := MemLp.of_eval_piLp hpLp
  have hE (i : ι) : ∫ ω, (X 0 ω) i ∂P = p i := by
    have hs : NullMeasurableSet {ω | Z 0 ω = i} P :=
      (hident 0).aemeasurable_fst.nullMeasurableSet_preimage (measurableSet_singleton i)
    rw [hcoord, integral_indicator₀ hs]
    simpa using hprob i
  have hmean : (∫ ω, X 0 ω ∂P) = WithLp.toLp 2 p := by
    ext i
    change EuclideanSpace.proj i (∫ ω, X 0 ω ∂P) = p i
    rw [← (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm (hX.integrable one_le_two)]
    exact hE i
  have hcov (i j : ι) : cov[fun ω => (X 0 ω) i, fun ω => (X 0 ω) j; P] = C i j := by
    rw [covariance_eq_sub (hpLp i) (hpLp j), hE i, hE j]
    by_cases hij : i = j
    · subst j
      have hmul : (fun ω => (X 0 ω) i) * (fun ω => (X 0 ω) i) = fun ω => (X 0 ω) i := by
        funext ω
        simp only [Pi.mul_apply, X, oneHot_apply]
        split <;> norm_num
      rw [hmul, hE i]
      simp [C, Matrix.vecMulVec_apply]
    · have hmul : (fun ω => (X 0 ω) i) * (fun ω => (X 0 ω) j) = fun _ => 0 := by
        funext ω
        simp only [Pi.mul_apply, X, oneHot_apply]
        split <;> split <;> simp_all
      rw [hmul, integral_zero]
      simp [C, Matrix.vecMulVec_apply, hij]
  have hbilin (x y : EuclideanSpace ℝ ι) : covarianceBilin (P.map (X 0)) x y = x ⬝ᵥ C *ᵥ y := by
    have h := covarianceBilin_apply_pi hpLp x y
    change covarianceBilin (P.map (X 0)) x y = _ at h
    rw [h]
    simp only [hcov, dotProduct, mulVec, Finset.mul_sum]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  have hpos : C.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · change Cᴴ = C
      ext i j
      by_cases hij : i = j
      · subst j
        simp [C, Matrix.vecMulVec_apply]
      · simp [C, Matrix.vecMulVec_apply, hij, Ne.symm hij, mul_comm]
    · simpa using (hbilin (WithLp.toLp 2 x) (WithLp.toLp 2 x)) ▸
          covarianceBilin_self_nonneg (μ := P.map (X 0)) (WithLp.toLp 2 x)
  have hnull : C *ᵥ (1 : ι → ℝ) = 0 := by
    funext i
    simp only [mulVec, dotProduct, Pi.one_apply, mul_one, Pi.zero_apply, C, Matrix.sub_apply,
      Matrix.diagonal_apply, Matrix.vecMulVec_apply, sum_sub_distrib]
    rw [← Finset.mul_sum, hpsum, mul_one]
    simp
  have hsing : ¬IsUnit C := by
    intro hu
    have h10 : (1 : ι → ℝ) = 0 := Matrix.mulVec_injective_iff_isUnit.mpr hu (by simpa using hnull)
    have hzero : (∑ i, p i) = 0 := by
      apply sum_eq_zero
      intro i _
      have hi : (1 : ℝ) = 0 := congrFun h10 i
      exact (one_ne_zero hi).elim
    exact one_ne_zero (hpsum.symm.trans hzero)
  obtain ⟨A, hG, hAmean, hAcov, hclt⟩ :=
    exists_tendstoInDistribution_sqrt_smul_mean_sub hX hindepX hidentX
  have : IsGaussian ((stdGaussian (EuclideanSpace ℝ ι)).map A) := hG.isGaussian_map
  have hmap : (stdGaussian (EuclideanSpace ℝ ι)).map A = multivariateGaussian 0 C := by
    apply IsGaussian.ext
    · rw [integral_map A.continuous.aemeasurable aestronglyMeasurable_id]
      simpa using hAmean
    · rw [hAcov]
      ext x y
      rw [hbilin, covarianceBilin_multivariateGaussian hpos]
  refine ⟨hmean, hcov, hpos, hnull, hsing, ?_, ?_⟩
  · rw [hmean] at hclt
    refine ⟨hclt.forall_aemeasurable, measurable_id.aemeasurable, ?_⟩
    convert hclt.tendsto using 1
    apply congrArg (fun ν : ProbabilityMeasure (EuclideanSpace ℝ ι) => 𝓝 ν)
    apply ProbabilityMeasure.toMeasure_injective
    change (multivariateGaussian 0 C).map id = (stdGaussian (EuclideanSpace ℝ ι)).map A
    rw [Measure.map_id, hmap]
  · intro i hi
    have he := (measurePreserving_eval_multivariateGaussian (μ := 0) hpos (i := i)).map_eq
    simpa [C, Matrix.diagonal_apply, Matrix.vecMulVec_apply, hi, gaussianReal_zero_var] using he

end ProbabilityTheory

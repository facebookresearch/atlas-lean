/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Data.PNat.Notation
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.Variance
public import MathlibExt.Probability.MonteCarloRate
public import MathlibExt.Probability.Statistics.SampleMoments

/-!

# Measurement uncertainty and its first-order propagation

Variances of linear and linearized measurement models, an explicit remainder bound for the
linearization, the first-order relative-uncertainty rule for power laws, unbiased estimation from
repeated observations, and significant-figure rounding as a reporting function.

## i. Overview

A measurement is modelled in the probabilistic language of the GUM. The input quantities are a
finite family of real random variables `X : ι → Ω → ℝ` on a probability space `(Ω, μ)` with finite
second moments, `MemLp (X i) 2 μ`. The standard uncertainty `u i` of an input is the standard
deviation of `X i`, so `Var[X i; μ] = u i ^ 2`, and correlations enter through
`cov[X i, X j; μ]`. The measurand is `Y = f X` for a measurement function `f : (ι → ℝ) → ℝ`,
expanded about the vector `x` of input estimates. In the vocabulary of OpenStax §1.5, variances
quantify precision (agreement of repeated measurements); accuracy (agreement with a true value)
concerns systematic error, which is not modelled here. The GUM's Type A evaluation (statistics of
repeated observations, section D) and Type B evaluation (other information) both end in such a
variance; the classification is vocabulary only.

Section A is the exact identity `Var[∑ i, a i * X i] = ∑ i, ∑ j, a i * a j * cov[X i, X j]`. It
is a specialization of Mathlib's `ProbabilityTheory.variance_fun_sum` and adds no variance API.

Section B states the GUM law of propagation of uncertainty as what it is: an exact identity for
the first-order Taylor linearization `f x + Df(x) (X - x)`, with sensitivity coefficients
`∂f/∂xᵢ (x) = fderiv ℝ f x (Pi.single i 1)`, together with an explicit remainder bound
`|f (x + h) - f x - Df(x) h| ≤ 1 / 2 * H * ‖h‖ ^ 2` when the second derivative is bounded by `H`
on a box. Norms on `ι → ℝ` are Mathlib's sup norm, and `H` bounds the operator norm of the second
derivative for that norm. For a nonlinear `f` the variance of `f X` itself differs from the
first-order value in general.

Section C applies section B to power laws `y = ∏ i, x i ^ p i` with integer exponents, covering
products, quotients and powers. For nonzero estimates and uncorrelated inputs it gives the
first-order rule `(u_y / y) ^ 2 = ∑ i, (p i * u i / x i) ^ 2`, which is also the first-order
variance of `Real.log y`, that is of `log |y|`.

Section D uses the canonical sample statistics: for `n ≥ 2` pairwise independent,
identically distributed observations with finite variance, the sample mean
`FiniteProbability.sampleMean` is unbiased for the mean and the `(n - 1)` sample variance
`FiniteProbability.sampleVarUnbiased` is unbiased for the variance, by
`MathlibExt.Probability.integral_sample_mean` and
`MathlibExt.Probability.integral_sampleVariance_of_pairwise_iid_fin`. This module defines no
sample-statistics API of its own.

Section E defines rounding to `k` significant figures, for a positive count `k : ℕ+`, as a
function `ℝ → ℝ` and proves that it is not an uncertainty calculus: rounding the inputs before
combining them can change the reported result. Significant figures are a reporting convention
only, never a substitute for the propagation laws of sections B and C. The type `ℕ+` excludes
`k = 0`, which has no significant-figure interpretation.

The results do not assert that the propagation law is exact for nonlinear measurement functions,
any coverage probability, coverage factor or expanded uncertainty, any normality of the inputs,
or that significant figures propagate uncertainty.

## ii. Key results

- `measurementFunction_variance_linearCombination` : the variance of `∑ i, a i * X i` is
  `∑ i, ∑ j, a i * a j * cov[X i, X j]`.
- `measurementFunction_variance_affineCombination` : the same with a constant offset.
- `measurementFunction_linearizedVariance_firstOrder` : the first-order law of propagation for
  correlated inputs.
- `measurementFunction_linearizedVariance_firstOrder_of_contDiffOn` : the same for a measurement
  function of class `C¹` on an open set containing the input estimate.
- `measurementFunction_linearizedVariance_firstOrder_uncorrelated` : the first-order law for
  uncorrelated inputs, `∑ i, (∂f/∂xᵢ (x) * u i) ^ 2`.
- `measurementFunction_firstOrder_remainder_le_of_hasFDerivAt` : the linearization error is at
  most `1 / 2 * H * ‖h‖ ^ 2` under a bound `H` on the second derivative over a box.
- `measurementFunction_firstOrder_remainder_le` : the same for a measurement function of class
  `C²` on an open set containing the box.
- `powerLaw` : the measurement function `∏ i, x i ^ p i`, with `hasFDerivAt_powerLaw` and
  `hasFDerivAt_log_powerLaw` giving `∂y/∂xᵢ = p i * y / x i` and `∂(log |y|)/∂xᵢ = p i / x i`.
- `relativeUncertainty_powerLaw_firstOrder` : the first-order relative-uncertainty rule
  `(u_y / y) ^ 2 = ∑ i, (p i * u i / x i) ^ 2`.
- `linearizedVariance_log_powerLaw_firstOrder` : the same sum is the first-order variance of
  `Real.log y = log |y|`.
- Section D sample statistics : the canonical `FiniteProbability.sampleMean` and
  `FiniteProbability.sampleVarUnbiased`; the sample mean is unbiased by
  `MathlibExt.Probability.integral_sample_mean`, and the `(n - 1)` sample variance is
  unbiased for `n ≥ 2` under pairwise independence by
  `MathlibExt.Probability.integral_sampleVariance_of_pairwise_iid_fin`.
- `roundSigFig` : rounding to `k` significant figures for a positive count `k : ℕ+`, well
  defined by `roundSigFig_wellDefined`, with `roundSigFig_eq_of_zpow_le_of_lt` and
  `abs_roundSigFig_sub_le` for its value and its half-unit rounding error.
- `exists_roundSigFig_add_ne` : rounding the inputs before adding can change the reported sum.

## iii. Table of contents

- A. Variance of linear and affine combinations
- B. First-order law of propagation and its remainder
- C. Relative uncertainty of power laws
- D. Sample mean and sample variance
- E. Significant figures as a reporting function

## iv. References

- JCGM 100:2008, *Guide to the Expression of Uncertainty in Measurement* (GUM), law of
  propagation of uncertainty.
- OpenStax, *Chemistry 2e*, §1.5, "Measurement Uncertainty, Accuracy, and Precision".
- OpenStax, *Chemistry 2e*, §1.6, "Mathematical Treatment of Measurement Results".

-/

@[expose] public section

namespace Chemistry.Uncertainty

open MeasureTheory ProbabilityTheory

/-!

## A. Variance of linear and affine combinations

-/

/-- The variance of a linear combination of input quantities with finite second moments on a
probability space is `Var[∑ i, a i * X i] = ∑ i, ∑ j, a i * a j * cov[X i, X j]`, exactly. This
is a specialization of Mathlib's `ProbabilityTheory.variance_fun_sum`, using
`MemLp.const_mul` and `covariance_const_mul_left` / `covariance_const_mul_right`. -/
lemma measurementFunction_variance_linearCombination {Ω ι : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype ι] (X : ι → Ω → ℝ) (a : ι → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ) :
    Var[fun ω => ∑ i, a i * X i ω; μ] = ∑ i, ∑ j, a i * a j * cov[X i, X j; μ] := by
  rw [variance_fun_sum fun i => (hX i).const_mul (a i)]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The variance of an affine combination `b + ∑ i, a i * X i` of input quantities with finite
second moments on a probability space: the constant offset `b` does not contribute
(`ProbabilityTheory.variance_const_add`). -/
lemma measurementFunction_variance_affineCombination {Ω ι : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype ι] (X : ι → Ω → ℝ) (a : ι → ℝ) (b : ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ) :
    Var[fun ω => b + ∑ i, a i * X i ω; μ] = ∑ i, ∑ j, a i * a j * cov[X i, X j; μ] :=
  (variance_const_add
      (memLp_finsetSum Finset.univ fun i _ => (hX i).const_mul (a i)).aestronglyMeasurable b).trans
    (measurementFunction_variance_linearCombination X a hX)

/-!

## B. First-order law of propagation and its remainder

-/

/-- **First-order law of propagation of uncertainty, correlated inputs.** If the measurement
function `f` has Fréchet derivative `f'` at the input estimate `x`, the variance of the
first-order Taylor linearization `ω ↦ f x + f' (X ω - x)` is
`∑ i, ∑ j, cᵢ * cⱼ * cov[X i, X j]`, where `cᵢ = ∂f/∂xᵢ (x) = fderiv ℝ f x (Pi.single i 1)` are
the sensitivity coefficients. It is `measurementFunction_variance_affineCombination` applied to
the coefficients `f' (Pi.single i 1)`, which equal `cᵢ` by `HasFDerivAt.fderiv`. The identity is
exact for the linearization only; for a nonlinear `f` it is not a statement about the variance of
`f X`, whose deviation from the linearization is controlled by
`measurementFunction_firstOrder_remainder_le`. -/
lemma measurementFunction_linearizedVariance_firstOrder {Ω ι : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ℝ} {f' : (ι → ℝ) →L[ℝ] ℝ} {x : ι → ℝ} (hf : HasFDerivAt f f' x)
    (X : ι → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) :
    Var[fun ω => f x + f' (fun i => X i ω - x i); μ] =
      ∑ i, ∑ j, fderiv ℝ f x (Pi.single i 1) * fderiv ℝ f x (Pi.single j 1) *
        cov[X i, X j; μ] := by
  have hcoord (v : ι → ℝ) : f' v = ∑ i, f' (Pi.single i 1) * v i := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsingle : Pi.single i (v i) = v i • (Pi.single i 1 : ι → ℝ) := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj]
    rw [hsingle, map_smul, smul_eq_mul, mul_comm]
  have hlin : (fun ω => f x + f' (fun i => X i ω - x i)) =
      fun ω => (f x - ∑ i, f' (Pi.single i 1) * x i) + ∑ i, f' (Pi.single i 1) * X i ω := by
    funext ω
    rw [hcoord (fun i => X i ω - x i)]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hf.fderiv, hlin]
  exact measurementFunction_variance_affineCombination X (fun i => f' (Pi.single i 1)) _ hX

/-- **First-order law of propagation for a `C¹` measurement function.** If `f` is of class `C¹`
on an open set `U` containing the input estimate `x` (for instance an open set containing a box
around `x`), then `fderiv ℝ f x` is the derivative of `f` at `x` and the first-order law
`measurementFunction_linearizedVariance_firstOrder` holds for the linearization
`ω ↦ f x + fderiv ℝ f x (X ω - x)`. -/
lemma measurementFunction_linearizedVariance_firstOrder_of_contDiffOn {Ω ι : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ℝ} {U : Set (ι → ℝ)} {x : ι → ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hx : x ∈ U) (X : ι → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) :
    Var[fun ω => f x + fderiv ℝ f x (fun i => X i ω - x i); μ] =
      ∑ i, ∑ j, fderiv ℝ f x (Pi.single i 1) * fderiv ℝ f x (Pi.single j 1) *
        cov[X i, X j; μ] :=
  measurementFunction_linearizedVariance_firstOrder
    ((hf.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt X hX

/-- **First-order law of propagation, uncorrelated inputs.** If `f` has derivative `f'` at `x`,
the inputs have standard uncertainties `u i` (`Var[X i] = u i ^ 2`) and are pairwise
uncorrelated, then the first-order combined variance is `∑ i, (∂f/∂xᵢ (x) * u i) ^ 2`. Only
`u i ^ 2` enters, so the sign convention `0 ≤ u i` is not needed. Pairwise independent inputs
are uncorrelated by `ProbabilityTheory.IndepFun.covariance_eq_zero`. -/
lemma measurementFunction_linearizedVariance_firstOrder_uncorrelated {Ω ι : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ℝ} {f' : (ι → ℝ) →L[ℝ] ℝ} {x : ι → ℝ} (hf : HasFDerivAt f f' x)
    (X : ι → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) (u : ι → ℝ) (hu : ∀ i, Var[X i; μ] = u i ^ 2)
    (hcov : ∀ i j, i ≠ j → cov[X i, X j; μ] = 0) :
    Var[fun ω => f x + f' (fun i => X i ω - x i); μ] =
      ∑ i, (fderiv ℝ f x (Pi.single i 1) * u i) ^ 2 := by
  rw [measurementFunction_linearizedVariance_firstOrder hf X hX]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hji => by rw [hcov i j (Ne.symm hji), mul_zero])
      (by simp), covariance_self (hX i).aemeasurable, hu i]
  ring

/-- **Explicit remainder of the first-order linearization.** Let `f` have derivative `f' y` at
every point `y` of the box `Set.Icc lo hi`, and let `f'` have derivative `f'' y` there, with
`‖f'' y‖ ≤ H` on the box. For `x` and `x + h` in the box, the error of the first-order Taylor
linearization is `|f (x + h) - f x - f' x h| ≤ 1 / 2 * H * ‖h‖ ^ 2`. The norm on `ι → ℝ` is the
sup norm and `‖f'' y‖` is the corresponding operator norm. The constant `1 / 2` is attained by
quadratic functions. The proof applies Mathlib's mean value inequality
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` to `f'` and the comparison theorem
`image_norm_le_of_norm_deriv_right_le_deriv_boundary` along the segment from `x` to `x + h`. -/
lemma measurementFunction_firstOrder_remainder_le_of_hasFDerivAt {ι : Type*} [Fintype ι]
    {f : (ι → ℝ) → ℝ} {f' : (ι → ℝ) → (ι → ℝ) →L[ℝ] ℝ}
    {f'' : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ} {lo hi x h : ι → ℝ} {H : ℝ}
    (hf : ∀ y ∈ Set.Icc lo hi, HasFDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc lo hi, HasFDerivAt f' (f'' y) y)
    (hH : ∀ y ∈ Set.Icc lo hi, ‖f'' y‖ ≤ H)
    (hx : x ∈ Set.Icc lo hi) (hxh : x + h ∈ Set.Icc lo hi) :
    |f (x + h) - f x - f' x h| ≤ 1 / 2 * H * ‖h‖ ^ 2 := by
  have hs : Convex ℝ (Set.Icc lo hi) := convex_Icc lo hi
  have hseg (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : x + t • h ∈ Set.Icc lo hi :=
    hs.add_smul_mem hx hxh ht
  have hlip (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖f' (x + t • h) - f' x‖ ≤ H * (t * ‖h‖) := by
    have := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun y hy => (hf' y hy).hasFDerivWithinAt) hH hx (hseg t ht)
    rwa [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1] at this
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ => f (x + s • h) - f x - s * f' x h)
        (f' (x + t • h) h - f' x h) t := by
    have hline : HasDerivAt (fun s : ℝ => x + s • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add x
    have hcomp := HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => x + s • h) t
      (hf _ (hseg t ht)) hline
    exact ((hcomp.sub_const (f x)).sub ((hasDerivAt_id t).mul_const (f' x h))).congr_deriv
      (by simp)
  have hbound := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun s : ℝ => f (x + s • h) - f x - s * f' x h)
    (f' := fun s => f' (x + s • h) h - f' x h)
    (B := fun s => H * ‖h‖ ^ 2 * s ^ 2 / 2) (B' := fun s => H * ‖h‖ ^ 2 * s) (a := 0) (b := 1)
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hderiv t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp)
    (fun t => by
      convert ((hasDerivAt_pow 2 t).const_mul (H * ‖h‖ ^ 2)).div_const 2 using 1
      ring)
    (fun t ht => by
      calc ‖f' (x + t • h) h - f' x h‖ = ‖(f' (x + t • h) - f' x) h‖ := by
            rw [sub_apply]
        _ ≤ ‖f' (x + t • h) - f' x‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ H * (t * ‖h‖) * ‖h‖ :=
            mul_le_mul_of_nonneg_right (hlip t (Set.Ico_subset_Icc_self ht)) (norm_nonneg h)
        _ = H * ‖h‖ ^ 2 * t := by ring)
  have h1 := hbound (Set.right_mem_Icc.2 zero_le_one)
  simp only [one_smul, one_mul, one_pow, mul_one, Real.norm_eq_abs] at h1
  linarith

/-- **Explicit first-order remainder for a `C²` measurement function.** If `f` is of class `C²`
on an open set `U` containing the box `Set.Icc lo hi` and its second derivative satisfies
`‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H` on the box, then for `x` and `x + h` in the box
`|f (x + h) - f x - fderiv ℝ f x h| ≤ 1 / 2 * H * ‖h‖ ^ 2`, for the sup norm on `ι → ℝ`. -/
lemma measurementFunction_firstOrder_remainder_le {ι : Type*} [Fintype ι]
    {f : (ι → ℝ) → ℝ} {U : Set (ι → ℝ)} {lo hi x h : ι → ℝ} {H : ℝ}
    (hU : IsOpen U) (hbox : Set.Icc lo hi ⊆ U) (hf : ContDiffOn ℝ 2 f U)
    (hH : ∀ y ∈ Set.Icc lo hi, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H)
    (hx : x ∈ Set.Icc lo hi) (hxh : x + h ∈ Set.Icc lo hi) :
    |f (x + h) - f x - fderiv ℝ f x h| ≤ 1 / 2 * H * ‖h‖ ^ 2 := by
  have hf1 : ContDiffOn ℝ 1 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by norm_num)
  refine measurementFunction_firstOrder_remainder_le_of_hasFDerivAt (fun y hy => ?_)
    (fun y hy => ?_) hH hx hxh
  · exact ((hf.differentiableOn (by norm_num) y (hbox hy)).differentiableAt
      (hU.mem_nhds (hbox hy))).hasFDerivAt
  · exact ((hf1.differentiableOn (by norm_num) y (hbox hy)).differentiableAt
      (hU.mem_nhds (hbox hy))).hasFDerivAt

/-!

## C. Relative uncertainty of power laws

-/

/-- The power-law measurement function `y = ∏ i, x i ^ p i` with integer exponents `p i`. It
covers products (`p i = 1`), quotients (`p i = -1` on the denominators) and powers. -/
noncomputable def powerLaw {ι : Type*} [Fintype ι] (p : ι → ℤ) (x : ι → ℝ) : ℝ :=
  ∏ i, x i ^ p i

/-- A power law with nonzero inputs is nonzero. -/
lemma powerLaw_ne_zero {ι : Type*} [Fintype ι] (p : ι → ℤ) {x : ι → ℝ} (hx : ∀ i, x i ≠ 0) :
    powerLaw p x ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hx i)

/-- At inputs with every `x i ≠ 0`, the power law has derivative `∑ i, (p i * y / x i) • dxᵢ`,
where `y = powerLaw p x`: the sensitivity coefficients are `∂y/∂xᵢ = p i * y / x i`. -/
lemma hasFDerivAt_powerLaw {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℤ) {x : ι → ℝ}
    (hx : ∀ i, x i ≠ 0) :
    HasFDerivAt (powerLaw p)
      (∑ i, (p i * powerLaw p x / x i) • (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) x := by
  have hcoord : ∀ i ∈ (Finset.univ : Finset ι), HasFDerivAt (fun ξ : ι → ℝ => ξ i ^ p i)
      (((p i : ℝ) * x i ^ (p i - 1)) • (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) x :=
    fun i _ => by
      have hproj : HasFDerivAt (fun ξ : ι → ℝ => ξ i)
          (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) x := hasFDerivAt_apply i x
      exact (hasDerivAt_zpow (p i) (x i) (Or.inl (hx i))).comp_hasFDerivAt x hproj
  convert HasFDerivAt.finsetProd hcoord using 1
  · rfl
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  congr 1
  rw [powerLaw, ← Finset.mul_prod_erase Finset.univ (fun j => x j ^ p j) (Finset.mem_univ i),
    zpow_sub_one₀ (hx i)]
  field_simp

/-- The sensitivity coefficients of a power law: `∂y/∂xᵢ (x) = p i * y / x i` when every
`x i ≠ 0`. -/
lemma fderiv_powerLaw_single {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℤ) {x : ι → ℝ}
    (hx : ∀ i, x i ≠ 0) (i : ι) :
    fderiv ℝ (powerLaw p) x (Pi.single i 1) = p i * powerLaw p x / x i := by
  rw [(hasFDerivAt_powerLaw p hx).fderiv]
  simp [Pi.single_apply]

/-- The gradient of the logarithm of a power law: `∂(log |y|)/∂xᵢ = p i / x i` when every
`x i ≠ 0`, where Mathlib's `Real.log y` is `log |y|` for `y < 0`. Equivalently
`∂y/∂xᵢ = y * (p i / x i)`. -/
lemma hasFDerivAt_log_powerLaw {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℤ)
    {x : ι → ℝ} (hx : ∀ i, x i ≠ 0) :
    HasFDerivAt (fun ξ => Real.log (powerLaw p ξ))
      (∑ i, ((p i : ℝ) / x i) • (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) x := by
  convert (hasFDerivAt_powerLaw p hx).log (powerLaw_ne_zero p hx) using 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  congr 1
  field_simp [powerLaw_ne_zero p hx]

/-- **First-order relative-uncertainty rule for products, quotients and powers.** Let
`y = ∏ i, x i ^ p i` with integer exponents `p i` and nonzero input estimates `x i ≠ 0`. Let the
inputs have standard uncertainties `u i` (`Var[X i] = u i ^ 2`) and be uncorrelated,
`cov[X i, X j] = 0` for `i ≠ j`. (Zero covariance is uncorrelatedness, not independence: dependent
variables can have zero covariance. Independence implies uncorrelatedness.) Then the first-order
combined standard
uncertainty `u_y`, the standard deviation of the linearization
`ω ↦ y + fderiv ℝ (powerLaw p) x (X ω - x)`, satisfies `(u_y / y) ^ 2 = ∑ i, (p i * u i / x i) ^ 2`.
It is the law `measurementFunction_linearizedVariance_firstOrder_uncorrelated` with the
sensitivity coefficients `y * (p i / x i)` of `fderiv_powerLaw_single`. The rule is first-order:
it is exact for the linearization, not for `y` evaluated at random inputs. -/
lemma relativeUncertainty_powerLaw_firstOrder {Ω ι : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype ι] [DecidableEq ι]
    (p : ι → ℤ) {x : ι → ℝ} (hx : ∀ i, x i ≠ 0) (u : ι → ℝ)
    (X : ι → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) (hu : ∀ i, Var[X i; μ] = u i ^ 2)
    (hcov : ∀ i j, i ≠ j → cov[X i, X j; μ] = 0) :
    (√(Var[fun ω => powerLaw p x + fderiv ℝ (powerLaw p) x (fun i => X i ω - x i); μ]) /
      powerLaw p x) ^ 2 = ∑ i, (p i * u i / x i) ^ 2 := by
  have hd := (hasFDerivAt_powerLaw p hx).differentiableAt.hasFDerivAt
  have hy := powerLaw_ne_zero p hx
  rw [div_pow, Real.sq_sqrt (variance_nonneg _ _),
    measurementFunction_linearizedVariance_firstOrder_uncorrelated hd X hX u hu hcov,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_powerLaw_single p hx i]
  field_simp

/-- **The relative-uncertainty rule as the first-order law for `log |y|`.** Under the
hypotheses of `relativeUncertainty_powerLaw_firstOrder`, the first-order variance of
`Real.log y` (which is `log |y|`, also for negative `y`), with sensitivity coefficients
`p i / x i` from `hasFDerivAt_log_powerLaw`, is the same sum `∑ i, (p i * u i / x i) ^ 2`. -/
lemma linearizedVariance_log_powerLaw_firstOrder {Ω ι : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype ι] [DecidableEq ι]
    (p : ι → ℤ) {x : ι → ℝ} (hx : ∀ i, x i ≠ 0) (u : ι → ℝ)
    (X : ι → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) (hu : ∀ i, Var[X i; μ] = u i ^ 2)
    (hcov : ∀ i j, i ≠ j → cov[X i, X j; μ] = 0) :
    Var[fun ω => Real.log (powerLaw p x) +
        fderiv ℝ (fun ξ => Real.log (powerLaw p ξ)) x (fun i => X i ω - x i); μ] =
      ∑ i, (p i * u i / x i) ^ 2 := by
  have hd := (hasFDerivAt_log_powerLaw p hx).differentiableAt.hasFDerivAt
  rw [measurementFunction_linearizedVariance_firstOrder_uncorrelated hd X hX u hu hcov]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hasFDerivAt_log_powerLaw p hx).fderiv]
  simp [Pi.single_apply]
  ring

/-!

## D. Sample mean and sample variance

No sample-statistics API is defined here. The estimators are the canonical
`MathlibExt.Probability.FiniteProbability.sampleMean` and
`MathlibExt.Probability.FiniteProbability.sampleVarUnbiased`, the sample mean is unbiased by
`MathlibExt.Probability.integral_sample_mean`, and the `(n - 1)` sample variance is unbiased
for `n ≥ 2` under pairwise independence (plus identical distribution and finite variance) by
`MathlibExt.Probability.integral_sampleVariance_of_pairwise_iid_fin`, whose pairwise
hypothesis is exactly what a GUM Type A evaluation needs: mutual independence is not
required. See the tests for the two-fair-tosses instantiation.

-/

/-!

## E. Significant figures as a reporting function

-/

/-- The decimal shift `k - 1 - ⌊log₁₀ |x|⌋` that moves the `k`-th significant digit of `x` to the
units place. With Mathlib's convention `Real.logb 10 0 = 0` it is `k - 1` at `x = 0`. The count
`k : ℕ+` is positive by type: `k = 0` has no significant-figure interpretation and is excluded. -/
noncomputable def sigFigShift (k : ℕ+) (x : ℝ) : ℤ :=
  (k : ℤ) - 1 - ⌊Real.logb 10 |x|⌋

/-- Rounding to `k` significant figures, for a positive count `k : ℕ+`, a reporting function
`ℝ → ℝ`: `roundSigFig k x = round (x * 10 ^ e) / 10 ^ e` with
`e = sigFigShift k x = k - 1 - ⌊log₁₀ |x|⌋`, so the result is an integer multiple of
`10 ^ (-e)`. Ties are rounded upward, since Mathlib's `round x = ⌊x + 1 / 2⌋`; OpenStax §1.5
instead rounds a dropped `5` to an even digit, and the conventions differ only at exact ties.
Significant figures are reporting only, never a substitute for the propagation laws of sections B
and C: see `exists_roundSigFig_add_ne`. -/
noncomputable def roundSigFig (k : ℕ+) (x : ℝ) : ℝ :=
  round (x * 10 ^ sigFigShift k x) / 10 ^ sigFigShift k x

/-- The decimal exponent `⌊log₁₀ |x|⌋` is the unique integer `m` with
`10 ^ m ≤ |x| < 10 ^ (m + 1)`. -/
lemma floor_logb_ten_abs_eq {x : ℝ} {m : ℤ} (h1 : (10 : ℝ) ^ m ≤ |x|)
    (h2 : |x| < 10 ^ (m + 1)) : ⌊Real.logb 10 |x|⌋ = m := by
  have hx : 0 < |x| := lt_of_lt_of_le (zpow_pos (by norm_num) m) h1
  have h10 : Real.logb 10 |x| = Real.logb ((10 : ℕ) : ℝ) |x| := by norm_num
  rw [h10, Real.floor_logb_natCast hx.le]
  apply le_antisymm
  · have := (Int.lt_zpow_iff_log_lt (b := 10) (by norm_num) hx).1 (by exact_mod_cast h2)
    omega
  · exact (Int.zpow_le_iff_le_log (b := 10) (by norm_num) hx).1 (by exact_mod_cast h1)

/-- If `10 ^ m ≤ |x| < 10 ^ (m + 1)`, rounding to `k` significant figures (for a positive
count `k : ℕ+`) rounds `x` at the decimal place `10 ^ (m + 1 - k)`. -/
lemma roundSigFig_eq_of_zpow_le_of_lt {k : ℕ+} {x : ℝ} {m : ℤ} (h1 : (10 : ℝ) ^ m ≤ |x|)
    (h2 : |x| < 10 ^ (m + 1)) :
    roundSigFig k x = round (x * 10 ^ ((k : ℤ) - 1 - m)) / 10 ^ ((k : ℤ) - 1 - m) := by
  rw [roundSigFig, sigFigShift, floor_logb_ten_abs_eq h1 h2]

/-- **Rounding to significant figures is well defined.** `roundSigFig k` is a total function
`ℝ → ℝ`, with ties broken by `round`. For `x ≠ 0` and a positive count `k : ℕ+` the textbook
description determines it: there is exactly one decimal exponent `m`, the place `10 ^ m` of the
leading significant digit, with `10 ^ m ≤ |x| < 10 ^ (m + 1)`, and `roundSigFig k x` rounds `x`
at the place `10 ^ (m + 1 - k)` for that `m`. -/
lemma roundSigFig_wellDefined (k : ℕ+) {x : ℝ} (hx : x ≠ 0) :
    ∃! m : ℤ, (10 : ℝ) ^ m ≤ |x| ∧ |x| < 10 ^ (m + 1) ∧
      roundSigFig k x = round (x * 10 ^ ((k : ℤ) - 1 - m)) / 10 ^ ((k : ℤ) - 1 - m) := by
  have hx' : 0 < |x| := abs_pos.2 hx
  have h1 : (10 : ℝ) ^ Int.log 10 |x| ≤ |x| := by
    exact_mod_cast Int.zpow_log_le_self (b := 10) (by norm_num) hx'
  have h2 : |x| < 10 ^ (Int.log 10 |x| + 1) := by
    exact_mod_cast Int.lt_zpow_succ_log_self (b := 10) (by norm_num) |x|
  refine ⟨Int.log 10 |x|, ⟨h1, h2, roundSigFig_eq_of_zpow_le_of_lt h1 h2⟩, ?_⟩
  rintro m ⟨hm1, hm2, -⟩
  rw [← floor_logb_ten_abs_eq hm1 hm2, ← floor_logb_ten_abs_eq h1 h2]

/-- Zero is reported as zero. -/
@[simp]
lemma roundSigFig_zero (k : ℕ+) : roundSigFig k 0 = 0 := by
  simp [roundSigFig]

/-- Rounding to `k` significant figures, for a positive count `k : ℕ+`, changes `x` by at most
half a unit in the last reported place, `10 ^ (-sigFigShift k x)`. -/
lemma abs_roundSigFig_sub_le (k : ℕ+) (x : ℝ) :
    |roundSigFig k x - x| ≤ 1 / 2 * 10 ^ (-sigFigShift k x) := by
  have hpos : (0 : ℝ) < 10 ^ sigFigShift k x := zpow_pos (by norm_num) _
  have hrw : roundSigFig k x - x =
      (round (x * 10 ^ sigFigShift k x) - x * 10 ^ sigFigShift k x) / 10 ^ sigFigShift k x := by
    rw [roundSigFig]
    field_simp
  rw [hrw, abs_div, abs_of_pos hpos, div_le_iff₀ hpos, zpow_neg, mul_assoc,
    inv_mul_cancel₀ hpos.ne', mul_one, abs_sub_comm]
  exact abs_sub_round _

/-- **Rounding is not an uncertainty calculus.** Rounding `a` and `b` to one significant figure,
adding, and rounding the sum can report a different value from rounding the exact sum `a + b`.
Witness: `a = b = 1.4`, where `1 + 1 = 2` is reported but `1.4 + 1.4 = 2.8` rounds to `3`.
Significant figures are reporting only, never a substitute for the propagation laws of sections
B and C. -/
lemma exists_roundSigFig_add_ne :
    ∃ a b : ℝ, roundSigFig 1 (roundSigFig 1 a + roundSigFig 1 b) ≠ roundSigFig 1 (a + b) := by
  refine ⟨7 / 5, 7 / 5, ?_⟩
  have h75 : roundSigFig 1 (7 / 5) = 1 := by
    rw [roundSigFig_eq_of_zpow_le_of_lt (m := 0) (by norm_num [abs_of_pos])
      (by norm_num [abs_of_pos])]
    have : round (7 / 5 : ℝ) = 1 := by
      rw [round_eq_iff]
      norm_num
    norm_num [this]
  have h2 : roundSigFig 1 2 = 2 := by
    rw [roundSigFig_eq_of_zpow_le_of_lt (m := 0) (by norm_num [abs_of_pos])
      (by norm_num [abs_of_pos])]
    norm_num
  have h145 : roundSigFig 1 (7 / 5 + 7 / 5) = 3 := by
    rw [roundSigFig_eq_of_zpow_le_of_lt (m := 0) (by norm_num [abs_of_pos])
      (by norm_num [abs_of_pos])]
    have : round (14 / 5 : ℝ) = 3 := by
      rw [round_eq_iff]
      norm_num
    norm_num [this]
  rw [h75, show (1 : ℝ) + 1 = 2 by norm_num, h2, h145]
  norm_num

end Chemistry.Uncertainty

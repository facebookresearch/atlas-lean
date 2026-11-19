/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.Uncertainty.Propagation
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Probability.Distributions.Uniform

/-!

# Tests for measurement uncertainty and its first-order propagation

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Chemistry.Uncertainty

namespace PhyslibExtTest.Chemistry.Uncertainty

/-! ### Variance of a combination of two input quantities -/

/-- The variance of `a X₀ + b X₁` is `a² Var[X₀] + 2 a b cov[X₀, X₁] + b² Var[X₁]`. -/
lemma variance_two_inputs {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Fin 2 → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) (a b : ℝ) :
    Var[fun ω => a * X 0 ω + b * X 1 ω; μ] =
      a ^ 2 * Var[X 0; μ] + 2 * a * b * cov[X 0, X 1; μ] + b ^ 2 * Var[X 1; μ] := by
  have h := measurementFunction_variance_linearCombination X ![a, b] hX
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [h, covariance_self (hX 0).aemeasurable, covariance_self (hX 1).aemeasurable,
    covariance_comm (X 1) (X 0)]
  ring

/-- A constant offset does not change the variance of a two-input combination. -/
lemma variance_two_inputs_affine {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Fin 2 → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) (a b c : ℝ) :
    Var[fun ω => c + (a * X 0 ω + b * X 1 ω); μ] =
      Var[fun ω => a * X 0 ω + b * X 1 ω; μ] := by
  have h := measurementFunction_variance_affineCombination X ![a, b] c hX
  have h' := measurementFunction_variance_linearCombination X ![a, b] hX
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h h'
  rw [h, h']

/-! ### Two independent tosses of a fair coin -/

/-- A fair coin: the uniform law on `Bool`. -/
noncomputable abbrev fairCoin : Measure Bool := Measure.uniformOfFinset Finset.univ

instance isProbabilityMeasure_fairCoin : IsProbabilityMeasure fairCoin :=
  ⟨by simp [Measure.uniformOfFinset_apply, ENNReal.div_self]⟩

/-- Two independent tosses of a fair coin. -/
noncomputable abbrev twoTosses : Measure (Fin 2 → Bool) := Measure.pi fun _ => fairCoin

/-- The indicator of heads on toss `i`. -/
def heads (i : Fin 2) (ω : Fin 2 → Bool) : ℝ := if ω i then 1 else 0

/-- Each of the four outcomes of two tosses has probability `1 / 4`. -/
lemma twoTosses_real_singleton (ω : Fin 2 → Bool) : twoTosses.real {ω} = 1 / 4 := by
  rw [measureReal_def, Measure.pi_singleton]
  simp [Measure.uniformOfFinset_apply_singleton]
  norm_num

/-- A sum over the four outcomes of two tosses. -/
lemma sum_fin_two_bool (F : (Fin 2 → Bool) → ℝ) :
    ∑ ω, F ω = F ![true, true] + F ![true, false] + F ![false, true] + F ![false, false] := by
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp F]
  simp [Fintype.sum_prod_type]
  ring

/-- An expectation over two tosses is the average over the four outcomes. -/
lemma integral_twoTosses (F : (Fin 2 → Bool) → ℝ) :
    ∫ ω, F ω ∂twoTosses =
      (F ![true, true] + F ![true, false] + F ![false, true] + F ![false, false]) / 4 := by
  rw [integral_fintype .of_finite]
  simp only [twoTosses_real_singleton, smul_eq_mul]
  rw [← Finset.mul_sum, sum_fin_two_bool]
  ring

/-- The two tosses are mutually independent. -/
lemma iIndepFun_heads : iIndepFun heads twoTosses :=
  iIndepFun_pi (X := fun _ (b : Bool) => if b then (1 : ℝ) else 0)
    fun _ => Measurable.of_discrete.aemeasurable

/-- The two tosses are identically distributed. -/
lemma identDistrib_heads (i : Fin 2) : IdentDistrib (heads i) (heads 0) twoTosses twoTosses :=
  (IdentDistrib.mk (measurable_pi_apply i).aemeasurable (measurable_pi_apply 0).aemeasurable
    ((measurePreserving_eval _ i).map_eq.trans
      (measurePreserving_eval (fun _ : Fin 2 => fairCoin) 0).map_eq.symm)).comp
    (u := fun b : Bool => if b then (1 : ℝ) else 0) Measurable.of_discrete

/-- Two-point random inputs on two fair tosses: `X i = x i ± u i`, independently, each sign with
probability `1 / 2`. -/
noncomputable def twoPointInputs (x u : Fin 2 → ℝ) (i : Fin 2) (ω : Fin 2 → Bool) : ℝ :=
  x i + u i * (2 * heads i ω - 1)

/-- The two-point input `x i ± u i` has standard uncertainty `u i`. -/
lemma variance_twoPointInputs (x u : Fin 2 → ℝ) (i : Fin 2) :
    Var[twoPointInputs x u i; twoTosses] = u i ^ 2 := by
  rw [variance_eq_sub MemLp.of_discrete, integral_twoTosses, integral_twoTosses]
  fin_cases i <;> simp [twoPointInputs, heads] <;> ring

/-- Distinct two-point inputs are uncorrelated. -/
lemma covariance_twoPointInputs (x u : Fin 2 → ℝ) (i j : Fin 2) (hij : i ≠ j) :
    cov[twoPointInputs x u i, twoPointInputs x u j; twoTosses] = 0 := by
  rw [covariance_eq_sub MemLp.of_discrete MemLp.of_discrete, integral_twoTosses,
    integral_twoTosses, integral_twoTosses]
  fin_cases i <;> fin_cases j <;> simp_all [twoPointInputs, heads] <;> ring

/-! ### (a) Worked example: density `ρ = m / V` -/

/-- Density is the power law with exponents `(1, -1)`. -/
lemma powerLaw_density (ξ : Fin 2 → ℝ) : powerLaw ![1, -1] ξ = ξ 0 / ξ 1 := by
  simp [powerLaw, Fin.prod_univ_two, div_eq_mul_inv]

/-- Input estimates: mass `m = 10 g` and volume `V = 2 mL`. -/
def densityEstimate : Fin 2 → ℝ := ![10, 2]

/-- Standard uncertainties: `u(m) = 0.1 g` and `u(V) = 0.05 mL`. -/
noncomputable def densityUncertainty : Fin 2 → ℝ := ![1 / 10, 1 / 20]

lemma densityEstimate_ne_zero : ∀ i, densityEstimate i ≠ 0 := by
  intro i
  fin_cases i <;> norm_num [densityEstimate]

/-- The estimated density is `ρ = 10 / 2 = 5 g/mL`. -/
lemma density_estimate : powerLaw ![1, -1] densityEstimate = 5 := by
  rw [powerLaw_density]
  norm_num [densityEstimate]

/-- The sensitivity coefficients are `∂ρ/∂m = 1 / V = 1 / 2` and `∂ρ/∂V = -m / V² = -5 / 2`. -/
lemma density_sensitivities :
    fderiv ℝ (powerLaw ![1, -1]) densityEstimate (Pi.single 0 1) = 1 / 2 ∧
      fderiv ℝ (powerLaw ![1, -1]) densityEstimate (Pi.single 1 1) = -5 / 2 := by
  rw [fderiv_powerLaw_single _ densityEstimate_ne_zero, fderiv_powerLaw_single _
    densityEstimate_ne_zero, density_estimate]
  norm_num [densityEstimate]

/-- Worked example: for uncorrelated inputs with these uncertainties, the first-order
propagated variance of the density is
`u_ρ² = (1 / 2 * 0.1)² + (5 / 2 * 0.05)² = 29 / 1600`, so `u_ρ ≈ 0.135 g/mL`. -/
lemma density_linearizedVariance {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Fin 2 → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ)
    (hu : ∀ i, Var[X i; μ] = densityUncertainty i ^ 2)
    (hcov : ∀ i j, i ≠ j → cov[X i, X j; μ] = 0) :
    Var[fun ω => powerLaw ![1, -1] densityEstimate + fderiv ℝ (powerLaw ![1, -1])
      densityEstimate (fun i => X i ω - densityEstimate i); μ] = 29 / 1600 := by
  have hd :=
    (hasFDerivAt_powerLaw ![1, -1] densityEstimate_ne_zero).differentiableAt.hasFDerivAt
  rw [measurementFunction_linearizedVariance_firstOrder_uncorrelated hd X hX
      densityUncertainty hu hcov, Fin.sum_univ_two, density_sensitivities.1,
    density_sensitivities.2]
  norm_num [densityUncertainty]

/-- The worked example is not vacuous: the two-point inputs `m = 10 ± 0.1` and `V = 2 ± 0.05` on
two fair tosses satisfy its hypotheses, so their first-order density variance is `29 / 1600`. -/
lemma density_linearizedVariance_twoPoint :
    Var[fun ω => powerLaw ![1, -1] densityEstimate + fderiv ℝ (powerLaw ![1, -1])
      densityEstimate
        (fun i => twoPointInputs densityEstimate densityUncertainty i ω - densityEstimate i);
      twoTosses] = 29 / 1600 :=
  density_linearizedVariance _ (fun _ => MemLp.of_discrete) (variance_twoPointInputs _ _)
    (covariance_twoPointInputs _ _)

/-- Worked example, relative form: `(u_ρ / ρ)² = (0.1 / 10)² + (0.05 / 2)² = 29 / 40000`. -/
lemma density_relativeUncertainty {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Fin 2 → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ)
    (hu : ∀ i, Var[X i; μ] = densityUncertainty i ^ 2)
    (hcov : ∀ i j, i ≠ j → cov[X i, X j; μ] = 0) :
    (√(Var[fun ω => powerLaw ![1, -1] densityEstimate + fderiv ℝ (powerLaw ![1, -1])
      densityEstimate (fun i => X i ω - densityEstimate i); μ]) /
        powerLaw ![1, -1] densityEstimate) ^ 2 = 29 / 40000 := by
  rw [relativeUncertainty_powerLaw_firstOrder ![1, -1] densityEstimate_ne_zero
    densityUncertainty X hX hu hcov]
  simp [Fin.sum_univ_two, densityEstimate, densityUncertainty]
  norm_num

/-- The same relative uncertainty is the first-order variance of `log ρ`. -/
lemma density_logUncertainty {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Fin 2 → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ)
    (hu : ∀ i, Var[X i; μ] = densityUncertainty i ^ 2)
    (hcov : ∀ i j, i ≠ j → cov[X i, X j; μ] = 0) :
    Var[fun ω => Real.log (powerLaw ![1, -1] densityEstimate) +
      fderiv ℝ (fun ξ => Real.log (powerLaw ![1, -1] ξ)) densityEstimate
        (fun i => X i ω - densityEstimate i); μ] = 29 / 40000 := by
  rw [linearizedVariance_log_powerLaw_firstOrder ![1, -1] densityEstimate_ne_zero
    densityUncertainty X hX hu hcov]
  simp [Fin.sum_univ_two, densityEstimate, densityUncertainty]
  norm_num

/-! ### Special cases of the relative-uncertainty rule -/

/-- First-order rule for the product `y = x₀ x₁`: `(u_y / y)² = (u₀ / x₀)² + (u₁ / x₁)²`. -/
lemma relativeUncertainty_mul_firstOrder {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {x : Fin 2 → ℝ} (hx : ∀ i, x i ≠ 0) (u : Fin 2 → ℝ)
    (X : Fin 2 → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) (hu : ∀ i, Var[X i; μ] = u i ^ 2)
    (hcov : ∀ i j, i ≠ j → cov[X i, X j; μ] = 0) :
    (√(Var[fun ω => powerLaw ![1, 1] x + fderiv ℝ (powerLaw ![1, 1]) x
      (fun i => X i ω - x i); μ]) / (x 0 * x 1)) ^ 2 =
        (u 0 / x 0) ^ 2 + (u 1 / x 1) ^ 2 := by
  have hy : powerLaw ![1, 1] x = x 0 * x 1 := by simp [powerLaw, Fin.prod_univ_two]
  rw [← hy, relativeUncertainty_powerLaw_firstOrder ![1, 1] hx u X hX hu hcov]
  simp [Fin.sum_univ_two]

/-- First-order rule for the quotient `y = x₀ / x₁`: `(u_y / y)² = (u₀ / x₀)² + (u₁ / x₁)²`. -/
lemma relativeUncertainty_div_firstOrder {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {x : Fin 2 → ℝ} (hx : ∀ i, x i ≠ 0) (u : Fin 2 → ℝ)
    (X : Fin 2 → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) (hu : ∀ i, Var[X i; μ] = u i ^ 2)
    (hcov : ∀ i j, i ≠ j → cov[X i, X j; μ] = 0) :
    (√(Var[fun ω => powerLaw ![1, -1] x + fderiv ℝ (powerLaw ![1, -1]) x
      (fun i => X i ω - x i); μ]) / (x 0 / x 1)) ^ 2 =
        (u 0 / x 0) ^ 2 + (u 1 / x 1) ^ 2 := by
  rw [← powerLaw_density, relativeUncertainty_powerLaw_firstOrder ![1, -1] hx u X hX hu hcov]
  simp [Fin.sum_univ_two, neg_div]

/-- First-order rule for the power `y = x₀ ^ n`: `(u_y / y)² = (n * u₀ / x₀)²`. -/
lemma relativeUncertainty_zpow_firstOrder {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (n : ℤ) {x : Fin 1 → ℝ} (hx : x 0 ≠ 0) (u : Fin 1 → ℝ)
    (X : Fin 1 → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) (hu : ∀ i, Var[X i; μ] = u i ^ 2) :
    (√(Var[fun ω => powerLaw ![n] x + fderiv ℝ (powerLaw ![n]) x
      (fun i => X i ω - x i); μ]) / x 0 ^ n) ^ 2 = (n * u 0 / x 0) ^ 2 := by
  have hx' : ∀ i, x i ≠ 0 := fun i => by
    rw [Subsingleton.elim i 0]
    exact hx
  have hy : powerLaw ![n] x = x 0 ^ n := by simp [powerLaw]
  rw [← hy, relativeUncertainty_powerLaw_firstOrder ![n] hx' u X hX hu
    (fun i j hij => absurd (Subsingleton.elim i j) hij)]
  simp

/-! ### (b) Boundary case: the first-order law is inexact for the product `x₀ x₁` -/

/-- The product measurement function `f(x₀, x₁) = x₀ x₁`. -/
def prodFun (ξ : Fin 2 → ℝ) : ℝ := ξ 0 * ξ 1

/-- The derivative of `prodFun` at `y`: `h ↦ y₀ h₁ + y₁ h₀`. -/
noncomputable def prodFun' (y : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  y 0 • ContinuousLinearMap.proj 1 + y 1 • ContinuousLinearMap.proj 0

/-- The constant second derivative of `prodFun`: `h ↦ (k ↦ h₀ k₁ + h₁ k₀)`. -/
noncomputable def prodFun'' : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ) +
    (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ)

lemma hasFDerivAt_prodFun (y : Fin 2 → ℝ) : HasFDerivAt prodFun (prodFun' y) y :=
  (hasFDerivAt_apply 0 y).mul (hasFDerivAt_apply 1 y)

lemma prodFun'_eq : prodFun' = ⇑prodFun'' := by
  funext y
  ext h
  simp [prodFun', prodFun'']

lemma hasFDerivAt_prodFun' (y : Fin 2 → ℝ) : HasFDerivAt prodFun' prodFun'' y := by
  rw [prodFun'_eq]
  exact prodFun''.hasFDerivAt

lemma fderiv_prodFun : fderiv ℝ prodFun = prodFun' :=
  funext fun y => (hasFDerivAt_prodFun y).fderiv

lemma contDiff_prodFun : ContDiff ℝ 2 prodFun :=
  (contDiff_apply ℝ (fun _ : Fin 2 => ℝ) 0).mul (contDiff_apply ℝ (fun _ : Fin 2 => ℝ) 1)

lemma norm_proj_fin_two_le (i : Fin 2) :
    ‖(ContinuousLinearMap.proj i : (Fin 2 → ℝ) →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => by
    simpa using norm_le_pi_norm h i

/-- The second derivative of `prodFun` has operator norm at most `H = 2` for the sup norm. -/
lemma norm_prodFun''_le : ‖prodFun''‖ ≤ 2 := by
  have h0 := norm_proj_fin_two_le 0
  have h1 := norm_proj_fin_two_le 1
  have hadd := norm_add_le
    ((ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ))
    ((ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ))
  rw [ContinuousLinearMap.norm_smulRight_apply,
    ContinuousLinearMap.norm_smulRight_apply] at hadd
  unfold prodFun''
  nlinarith [norm_nonneg (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ),
    norm_nonneg (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ)]

/-- The input estimate `x = (2, 3)`. -/
def prodPoint : Fin 2 → ℝ := ![2, 3]

/-- The displacement `h = (0.1, 0.2)`, which is also the vector of input uncertainties below. -/
noncomputable def prodStep : Fin 2 → ℝ := ![1 / 10, 1 / 5]

lemma norm_prodStep : ‖prodStep‖ = 1 / 5 := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
    fin_cases i <;> norm_num [prodStep, abs_of_pos]
  · simpa [prodStep] using norm_le_pi_norm prodStep 1

lemma prodPoint_mem_box : prodPoint ∈ Set.Icc ![0, 0] ![3, 4] := by
  simp only [Set.mem_Icc, Pi.le_def, Fin.forall_fin_two]
  norm_num [prodPoint]

lemma prodPoint_add_prodStep_mem_box : prodPoint + prodStep ∈ Set.Icc ![0, 0] ![3, 4] := by
  simp only [Set.mem_Icc, Pi.le_def, Fin.forall_fin_two, Pi.add_apply]
  norm_num [prodPoint, prodStep]

/-- The exact value `f(x + h) = 2.1 * 3.2 = 6.72` and the first-order value
`f(x) + Df(x) h = 6 + 0.7 = 6.7` differ by the remainder `h₀ h₁ = 1 / 50`. -/
lemma prodFun_exact_ne_firstOrder :
    prodFun (prodPoint + prodStep) = 168 / 25 ∧
      prodFun prodPoint + prodFun' prodPoint prodStep = 67 / 10 ∧
      prodFun (prodPoint + prodStep) - prodFun prodPoint - prodFun' prodPoint prodStep =
        1 / 50 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [prodFun, prodFun', prodPoint, prodStep]

/-- The remainder bound with `H = 2` on the box `[0, 3] × [0, 4]` holds,
`|1 / 50| ≤ 1 / 2 * 2 * ‖h‖² = 1 / 25`, and the remainder is nonzero. -/
lemma prodFun_remainder_bound :
    |prodFun (prodPoint + prodStep) - prodFun prodPoint - prodFun' prodPoint prodStep| ≤
        1 / 2 * 2 * ‖prodStep‖ ^ 2 ∧
      1 / 2 * 2 * ‖prodStep‖ ^ 2 = (1 / 25 : ℝ) ∧
      prodFun (prodPoint + prodStep) - prodFun prodPoint - prodFun' prodPoint prodStep ≠ 0 := by
  refine ⟨measurementFunction_firstOrder_remainder_le_of_hasFDerivAt
    (f'' := fun _ => prodFun'') (fun y _ => hasFDerivAt_prodFun y)
    (fun y _ => hasFDerivAt_prodFun' y) (fun _ _ => norm_prodFun''_le) prodPoint_mem_box
    prodPoint_add_prodStep_mem_box, ?_, ?_⟩
  · rw [norm_prodStep]
    norm_num
  · rw [prodFun_exact_ne_firstOrder.2.2]
    norm_num

/-- The `C²` form of the remainder bound applies to `prodFun` with `U = Set.univ`. -/
lemma prodFun_remainder_bound_of_contDiff :
    |prodFun (prodPoint + prodStep) - prodFun prodPoint -
        fderiv ℝ prodFun prodPoint prodStep| ≤ 1 / 2 * 2 * ‖prodStep‖ ^ 2 :=
  measurementFunction_firstOrder_remainder_le isOpen_univ (Set.subset_univ _)
    contDiff_prodFun.contDiffOn
    (fun y _ => by
      rw [fderiv_prodFun, (hasFDerivAt_prodFun' y).fderiv]
      exact norm_prodFun''_le)
    prodPoint_mem_box prodPoint_add_prodStep_mem_box

/-- With independent two-point inputs `X₀ = 2 ± 0.1` and `X₁ = 3 ± 0.2`, the first-order law
gives `Var[X₀ X₁] ≈ (3 * 0.1)² + (2 * 0.2)² = 1 / 4`. -/
lemma prodFun_linearizedVariance_twoPoint :
    Var[fun ω => prodFun prodPoint +
      prodFun' prodPoint (fun i => twoPointInputs prodPoint prodStep i ω - prodPoint i);
      twoTosses] = 1 / 4 := by
  rw [measurementFunction_linearizedVariance_firstOrder_uncorrelated (hasFDerivAt_prodFun _)
    (twoPointInputs prodPoint prodStep) (fun _ => MemLp.of_discrete) prodStep
    (variance_twoPointInputs _ _) (covariance_twoPointInputs _ _), fderiv_prodFun]
  simp [Fin.sum_univ_two, prodFun', prodPoint, prodStep]
  norm_num

/-- The `C¹` form of the first-order law applies to `prodFun` with `U = Set.univ` and gives the
same first-order variance `1 / 4` for the two-point inputs. -/
lemma prodFun_linearizedVariance_of_contDiff :
    Var[fun ω => prodFun prodPoint +
      fderiv ℝ prodFun prodPoint (fun i => twoPointInputs prodPoint prodStep i ω - prodPoint i);
      twoTosses] = 1 / 4 := by
  rw [measurementFunction_linearizedVariance_firstOrder_of_contDiffOn isOpen_univ
    (contDiff_prodFun.of_le (by norm_num)).contDiffOn (Set.mem_univ _) _
    (fun _ => MemLp.of_discrete), Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two,
    covariance_self Measurable.of_discrete.aemeasurable,
    covariance_self Measurable.of_discrete.aemeasurable,
    covariance_twoPointInputs _ _ 0 1 (by decide), covariance_twoPointInputs _ _ 1 0 (by decide),
    variance_twoPointInputs, variance_twoPointInputs, fderiv_prodFun]
  simp [prodFun', prodPoint, prodStep]
  norm_num

/-- Correlated inputs: if both inputs are the same random variable `Y`, the first-order law,
including the cross terms `2 c₀ c₁ cov[Y, Y]`, gives `(3 + 2)² Var[Y] = 25 Var[Y]`. -/
lemma prodFun_linearizedVariance_correlated {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (Y : Ω → ℝ) (hY : MemLp Y 2 μ) :
    Var[fun ω => prodFun prodPoint + prodFun' prodPoint (fun i => Y ω - prodPoint i); μ] =
      25 * Var[Y; μ] := by
  rw [measurementFunction_linearizedVariance_firstOrder (hasFDerivAt_prodFun _) (fun _ => Y)
    (fun _ => hY), fderiv_prodFun]
  simp [Fin.sum_univ_two, prodFun', prodPoint, covariance_self hY.aemeasurable]
  ring

/-- The exact variance of `X₀ X₁` for the same inputs is
`x₀² u₁² + x₁² u₀² + u₀² u₁² = 313 / 1250 = 0.2504`, not the first-order value `1 / 4`: the
propagation law is not exact for this nonlinear `f`. -/
lemma prodFun_exactVariance_twoPoint :
    Var[fun ω => prodFun fun i => twoPointInputs prodPoint prodStep i ω; twoTosses] =
        313 / 1250 ∧
      (313 / 1250 : ℝ) ≠ 1 / 4 := by
  refine ⟨?_, by norm_num⟩
  rw [variance_eq_sub MemLp.of_discrete, integral_twoTosses, integral_twoTosses]
  norm_num [prodFun, twoPointInputs, heads, prodPoint, prodStep]

/-- The square `f(x₀) = x₀ x₀` in one variable. -/
def sqFun (ξ : Fin 1 → ℝ) : ℝ := ξ 0 * ξ 0

/-- The derivative of `sqFun` at `y`: `h ↦ 2 y₀ h₀`. -/
noncomputable def sqFun' (y : Fin 1 → ℝ) : (Fin 1 → ℝ) →L[ℝ] ℝ :=
  y 0 • ContinuousLinearMap.proj 0 + y 0 • ContinuousLinearMap.proj 0

/-- The constant second derivative of `sqFun`: `h ↦ (k ↦ 2 h₀ k₀)`. -/
noncomputable def sqFun'' : (Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ) +
    (ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ)

lemma norm_fin_one (h : Fin 1 → ℝ) : ‖h‖ = |h 0| := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun i => ?_
    rw [Subsingleton.elim i 0, Real.norm_eq_abs]
  · simpa using norm_le_pi_norm h 0

lemma norm_sqFun''_le : ‖sqFun''‖ ≤ 2 := by
  have hp : ‖(ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => by
      simpa using norm_le_pi_norm h 0
  have hadd := norm_add_le
    ((ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ))
    ((ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ))
  rw [ContinuousLinearMap.norm_smulRight_apply] at hadd
  unfold sqFun''
  nlinarith [norm_nonneg (ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ)]

/-- For `f(x₀) = x₀²` and `H = 2` the remainder bound holds with equality at every `x` and `h`,
so the constant `1 / 2` cannot be improved. -/
lemma sqFun_remainder_eq (x h : Fin 1 → ℝ) :
    |sqFun (x + h) - sqFun x - sqFun' x h| = 1 / 2 * 2 * ‖h‖ ^ 2 ∧
      |sqFun (x + h) - sqFun x - sqFun' x h| ≤ 1 / 2 * 2 * ‖h‖ ^ 2 := by
  have hsq : sqFun (x + h) - sqFun x - sqFun' x h = h 0 ^ 2 := by
    simp [sqFun, sqFun']
    ring
  have heq : |sqFun (x + h) - sqFun x - sqFun' x h| = 1 / 2 * 2 * ‖h‖ ^ 2 := by
    rw [hsq, norm_fin_one, abs_of_nonneg (sq_nonneg _), sq_abs]
    ring
  refine ⟨heq, ?_⟩
  have hsqd (y : Fin 1 → ℝ) : HasFDerivAt sqFun (sqFun' y) y :=
    (hasFDerivAt_apply 0 y).mul (hasFDerivAt_apply 0 y)
  have hsqd' : sqFun' = ⇑sqFun'' := by
    funext y
    ext k
    simp [sqFun', sqFun'']
  refine measurementFunction_firstOrder_remainder_le_of_hasFDerivAt (lo := x - fun _ => |h 0|)
    (hi := x + fun _ => |h 0|) (f'' := fun _ => sqFun'') (fun y _ => hsqd y)
    (fun y _ => by
      rw [hsqd']
      exact sqFun''.hasFDerivAt) (fun _ _ => norm_sqFun''_le) ?_ ?_
  · simp only [Set.mem_Icc, Pi.le_def, Pi.sub_apply, Pi.add_apply]
    exact ⟨fun _ => by linarith [abs_nonneg (h 0)], fun _ => by linarith [abs_nonneg (h 0)]⟩
  · simp only [Set.mem_Icc, Pi.le_def, Pi.sub_apply, Pi.add_apply]
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> rw [Subsingleton.elim i 0] <;>
      linarith [neg_abs_le (h 0), le_abs_self (h 0)]

/-! ### (c) Unbiasedness on two fair coin tosses (`n = 2`) -/

/-- `E[X̄] = E[X₀] = 1 / 2` for two fair tosses, for the canonical sample mean. -/
lemma integral_sampleMean_heads :
    ∫ ω, MathlibExt.Probability.FiniteProbability.sampleMean (fun i => heads i ω) ∂twoTosses =
      ∫ ω, heads 0 ω ∂twoTosses ∧
      ∫ ω, heads 0 ω ∂twoTosses = 1 / 2 := by
  refine ⟨?_, ?_⟩
  · simp only [MathlibExt.Probability.FiniteProbability.sampleMean_eq_sum_div]
    exact MathlibExt.Probability.integral_sample_mean (fun i => Integrable.of_finite)
      (fun i => (identDistrib_heads i).integral_eq)
  · rw [integral_twoTosses]
    norm_num [heads]

/-- The variance of one fair toss is `Var[X₀] = 1 / 4`. -/
lemma variance_heads : Var[heads 0; twoTosses] = 1 / 4 := by
  rw [variance_eq_sub MemLp.of_discrete, integral_twoTosses, integral_twoTosses]
  norm_num [heads]

/-- Computed directly over the four outcomes, `E[s²] = (0 + 1 / 2 + 1 / 2 + 0) / 4 = 1 / 4`,
for the canonical unbiased sample variance. -/
lemma integral_sampleVariance_heads :
    ∫ ω, MathlibExt.Probability.FiniteProbability.sampleVarUnbiased (fun i => heads i ω)
      ∂twoTosses = 1 / 4 := by
  rw [integral_twoTosses]
  simp only [MathlibExt.Probability.FiniteProbability.sampleVarUnbiased_eq_sum_div,
    MathlibExt.Probability.FiniteProbability.sampleMean_eq_sum_div, Fintype.card_fin,
    Fin.sum_univ_two, heads]
  norm_num

/-- The general theorem gives the same value: `E[s²] = Var[X₀]` for the pairwise-independent
tosses, via the pairwise-independence generalization in `SampleMoments`. -/
lemma integral_sampleVariance_heads_eq_variance :
    ∫ ω, MathlibExt.Probability.FiniteProbability.sampleVarUnbiased (fun i => heads i ω)
      ∂twoTosses = Var[heads 0; twoTosses] :=
  (MathlibExt.Probability.integral_sampleVariance_of_pairwise_iid_fin le_rfl heads 0
    (fun _ _ hij => iIndepFun_heads.indepFun hij) identDistrib_heads MemLp.of_discrete).2

/-- With `1 / n` in place of `1 / (n - 1)` the estimator is biased: its mean is
`1 / 8 ≠ 1 / 4 = Var[X₀]`. -/
lemma integral_biasedVariance_heads :
    ∫ ω, 1 / 2 * ∑ i, (heads i ω -
      MathlibExt.Probability.FiniteProbability.sampleMean (fun i => heads i ω)) ^ 2
      ∂twoTosses = 1 / 8 ∧
      (1 / 8 : ℝ) ≠ Var[heads 0; twoTosses] := by
  refine ⟨?_, by rw [variance_heads]; norm_num⟩
  rw [integral_twoTosses]
  simp only [MathlibExt.Probability.FiniteProbability.sampleMean_eq_sum_div, Fintype.card_fin,
    Fin.sum_univ_two, heads]
  norm_num

/-! ### (d) Significant figures are not an uncertainty calculus -/

/-- Evaluate `roundSigFig k x` from the decimal exponent `m` of `x` and the rounded integer `n`. -/
lemma roundSigFig_eq_of_mem {k : ℕ+} {x : ℝ} (m n : ℤ) (h1 : (10 : ℝ) ^ m ≤ |x|)
    (h2 : |x| < 10 ^ (m + 1))
    (hn : x * 10 ^ ((k : ℤ) - 1 - m) ∈ Set.Ico (n - 1 / 2 : ℝ) (n + 1 / 2)) :
    roundSigFig k x = n / 10 ^ ((k : ℤ) - 1 - m) := by
  rw [roundSigFig_eq_of_zpow_le_of_lt h1 h2, round_eq_iff.2 hn]

/-- `1.4` to one significant figure is `1`. -/
lemma roundSigFig_one_seven_fifths : roundSigFig 1 (7 / 5) = 1 := by
  rw [roundSigFig_eq_of_mem 0 1 (by norm_num [abs_of_pos]) (by norm_num [abs_of_pos])
    (by norm_num)]
  norm_num

/-- `2` to one significant figure is `2`. -/
lemma roundSigFig_one_two : roundSigFig 1 2 = 2 := by
  rw [roundSigFig_eq_of_mem 0 2 (by norm_num [abs_of_pos]) (by norm_num [abs_of_pos])
    (by norm_num)]
  norm_num

/-- `2.8` to one significant figure is `3`. -/
lemma roundSigFig_one_fourteen_fifths : roundSigFig 1 (14 / 5) = 3 := by
  rw [roundSigFig_eq_of_mem 0 3 (by norm_num [abs_of_pos]) (by norm_num [abs_of_pos])
    (by norm_num)]
  norm_num

/-- Rounding `1.4` and `1.4` and adding gives `2`; rounding `1.4 + 1.4 = 2.8` gives `3`. -/
lemma roundSigFig_counterexample :
    roundSigFig 1 (7 / 5) + roundSigFig 1 (7 / 5) ≠ roundSigFig 1 (7 / 5 + 7 / 5) ∧
      roundSigFig 1 (roundSigFig 1 (7 / 5) + roundSigFig 1 (7 / 5)) ≠
        roundSigFig 1 (7 / 5 + 7 / 5) := by
  rw [show (7 / 5 + 7 / 5 : ℝ) = 14 / 5 by norm_num, roundSigFig_one_seven_fifths,
    roundSigFig_one_fourteen_fifths, show (1 : ℝ) + 1 = 2 by norm_num, roundSigFig_one_two]
  norm_num

/-- The counterexample statement of the module. -/
lemma roundSigFig_counterexample_exists :
    ∃ a b : ℝ, roundSigFig 1 (roundSigFig 1 a + roundSigFig 1 b) ≠ roundSigFig 1 (a + b) :=
  exists_roundSigFig_add_ne

/-- `1234.5` to three significant figures is `1230`. -/
lemma roundSigFig_three : roundSigFig 3 (12345 / 10) = 1230 := by
  rw [roundSigFig_eq_of_mem 3 123 (by norm_num [abs_of_pos]) (by norm_num [abs_of_pos])
    (by norm_num)]
  norm_num

/-- `0.012345` to two significant figures is `0.012`. -/
lemma roundSigFig_two_small : roundSigFig 2 (12345 / 1000000) = 12 / 1000 := by
  rw [roundSigFig_eq_of_mem (-2) 12 (by norm_num [abs_of_pos]) (by norm_num [abs_of_pos])
    (by norm_num)]
  norm_num

/-- Rounding `1234.5` to three significant figures moves it by at most half of `10`. -/
lemma abs_roundSigFig_three_sub_le : |roundSigFig 3 (12345 / 10) - 12345 / 10| ≤ 5 := by
  have hs : sigFigShift 3 (12345 / 10) = -1 := by
    rw [sigFigShift, floor_logb_ten_abs_eq (m := 3) (by norm_num [abs_of_pos])
      (by norm_num [abs_of_pos])]
    norm_num
  calc |roundSigFig 3 (12345 / 10) - 12345 / 10|
      ≤ 1 / 2 * 10 ^ (-sigFigShift 3 (12345 / 10)) := abs_roundSigFig_sub_le 3 (12345 / 10)
    _ = 5 := by
      rw [hs]
      norm_num

/-- At `x = 1234.5` the unique decimal exponent of `roundSigFig_wellDefined` is `m = 3`. -/
lemma roundSigFig_wellDefined_three (m : ℤ)
    (hm : (10 : ℝ) ^ m ≤ |(12345 / 10 : ℝ)| ∧ |(12345 / 10 : ℝ)| < 10 ^ (m + 1) ∧
      roundSigFig 3 (12345 / 10) =
        round ((12345 / 10 : ℝ) * 10 ^ ((3 : ℤ) - 1 - m)) / 10 ^ ((3 : ℤ) - 1 - m)) :
    m = 3 := by
  obtain ⟨m₀, -, huniq⟩ := roundSigFig_wellDefined 3 (x := 12345 / 10) (by norm_num)
  have hb1 : (10 : ℝ) ^ (3 : ℤ) ≤ |(12345 / 10 : ℝ)| := by norm_num [abs_of_pos]
  have hb2 : |(12345 / 10 : ℝ)| < 10 ^ ((3 : ℤ) + 1) := by norm_num [abs_of_pos]
  rw [huniq m hm, huniq 3 ⟨hb1, hb2, roundSigFig_eq_of_zpow_le_of_lt hb1 hb2⟩]

/-- Zero is reported as zero. -/
lemma roundSigFig_zero_two : roundSigFig 2 0 = 0 :=
  roundSigFig_zero 2

/-! ### (e) The relative-uncertainty rule needs nonzero estimates -/

/-- The input estimate `x = (0, 2)`, with a zero entry. -/
def zeroEstimate : Fin 2 → ℝ := ![0, 2]

/-- Standard uncertainties `u = (0.1, 0.1)`. -/
noncomputable def zeroUncertainty : Fin 2 → ℝ := ![1 / 10, 1 / 10]

/-- At `x = (0, 2)` the hypothesis `∀ i, x i ≠ 0` of the relative-uncertainty rule fails. -/
lemma zeroEstimate_hypothesis_fails : ¬ ∀ i, zeroEstimate i ≠ 0 :=
  fun h => h 0 rfl

/-- Without `x i ≠ 0` the rule is false. The two-point inputs `X₀ = 0 ± 0.1` and `X₁ = 2 ± 0.1`
satisfy every other hypothesis of `relativeUncertainty_powerLaw_firstOrder` (finite variance,
`Var[X i] = u i ^ 2`, zero covariance), but its conclusion fails for the product `y = x₀ x₁` at
`x = (0, 2)`: `y = 0`, so the left side is `0` (Lean's `a / 0 = 0`), while the right side is
`(0.1 / 2)² ≠ 0`. -/
lemma relativeUncertainty_fails_at_zero :
    (∀ i, MemLp (twoPointInputs zeroEstimate zeroUncertainty i) 2 twoTosses) ∧
      (∀ i, Var[twoPointInputs zeroEstimate zeroUncertainty i; twoTosses] =
        zeroUncertainty i ^ 2) ∧
      (∀ i j, i ≠ j → cov[twoPointInputs zeroEstimate zeroUncertainty i,
        twoPointInputs zeroEstimate zeroUncertainty j; twoTosses] = 0) ∧
      (√(Var[fun ω => powerLaw ![1, 1] zeroEstimate + fderiv ℝ (powerLaw ![1, 1]) zeroEstimate
        (fun i => twoPointInputs zeroEstimate zeroUncertainty i ω - zeroEstimate i);
          twoTosses]) / powerLaw ![1, 1] zeroEstimate) ^ 2 ≠
        ∑ i, ((![1, 1] : Fin 2 → ℤ) i * zeroUncertainty i / zeroEstimate i) ^ 2 := by
  refine ⟨fun _ => MemLp.of_discrete, variance_twoPointInputs _ _,
    covariance_twoPointInputs _ _, ?_⟩
  have hy : powerLaw ![1, 1] zeroEstimate = 0 := by
    simp [powerLaw, Fin.prod_univ_two, zeroEstimate]
  rw [hy, div_zero]
  norm_num [Fin.sum_univ_two, zeroEstimate, zeroUncertainty]

/-- At `x = (0, 2)` the absolute first-order law still applies, `u_y² = (2 u₀)² = 1 / 25`, while
`y = 0`: no finite relative uncertainty exists. -/
lemma prodFun_linearizedVariance_at_zero {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Fin 2 → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ)
    (hu : ∀ i, Var[X i; μ] = zeroUncertainty i ^ 2)
    (hcov : ∀ i j, i ≠ j → cov[X i, X j; μ] = 0) :
    Var[fun ω => prodFun zeroEstimate + prodFun' zeroEstimate (fun i => X i ω - zeroEstimate i);
      μ] = 1 / 25 ∧ prodFun zeroEstimate = 0 := by
  refine ⟨?_, by norm_num [prodFun, zeroEstimate]⟩
  rw [measurementFunction_linearizedVariance_firstOrder_uncorrelated (hasFDerivAt_prodFun _)
    X hX _ hu hcov, fderiv_prodFun]
  simp [Fin.sum_univ_two, prodFun', zeroEstimate, zeroUncertainty]
  norm_num

end PhyslibExtTest.Chemistry.Uncertainty

#print axioms Chemistry.Uncertainty.measurementFunction_variance_linearCombination
#print axioms Chemistry.Uncertainty.measurementFunction_variance_affineCombination
#print axioms Chemistry.Uncertainty.measurementFunction_linearizedVariance_firstOrder
#print axioms Chemistry.Uncertainty.measurementFunction_linearizedVariance_firstOrder_of_contDiffOn
#print axioms Chemistry.Uncertainty.measurementFunction_linearizedVariance_firstOrder_uncorrelated
#print axioms Chemistry.Uncertainty.measurementFunction_firstOrder_remainder_le_of_hasFDerivAt
#print axioms Chemistry.Uncertainty.measurementFunction_firstOrder_remainder_le
#print axioms Chemistry.Uncertainty.powerLaw
#print axioms Chemistry.Uncertainty.powerLaw_ne_zero
#print axioms Chemistry.Uncertainty.hasFDerivAt_powerLaw
#print axioms Chemistry.Uncertainty.fderiv_powerLaw_single
#print axioms Chemistry.Uncertainty.hasFDerivAt_log_powerLaw
#print axioms Chemistry.Uncertainty.relativeUncertainty_powerLaw_firstOrder
#print axioms Chemistry.Uncertainty.linearizedVariance_log_powerLaw_firstOrder
#print axioms MathlibExt.Probability.integral_sampleVariance_of_pairwise_iid_fin
#print axioms Chemistry.Uncertainty.sigFigShift
#print axioms Chemistry.Uncertainty.roundSigFig
#print axioms Chemistry.Uncertainty.floor_logb_ten_abs_eq
#print axioms Chemistry.Uncertainty.roundSigFig_eq_of_zpow_le_of_lt
#print axioms Chemistry.Uncertainty.roundSigFig_wellDefined
#print axioms Chemistry.Uncertainty.roundSigFig_zero
#print axioms Chemistry.Uncertainty.abs_roundSigFig_sub_le
#print axioms Chemistry.Uncertainty.exists_roundSigFig_add_ne

#print axioms PhyslibExtTest.Chemistry.Uncertainty.variance_two_inputs
#print axioms PhyslibExtTest.Chemistry.Uncertainty.variance_two_inputs_affine
#print axioms PhyslibExtTest.Chemistry.Uncertainty.isProbabilityMeasure_fairCoin
#print axioms PhyslibExtTest.Chemistry.Uncertainty.twoTosses_real_singleton
#print axioms PhyslibExtTest.Chemistry.Uncertainty.sum_fin_two_bool
#print axioms PhyslibExtTest.Chemistry.Uncertainty.integral_twoTosses
#print axioms PhyslibExtTest.Chemistry.Uncertainty.iIndepFun_heads
#print axioms PhyslibExtTest.Chemistry.Uncertainty.identDistrib_heads
#print axioms PhyslibExtTest.Chemistry.Uncertainty.variance_twoPointInputs
#print axioms PhyslibExtTest.Chemistry.Uncertainty.covariance_twoPointInputs
#print axioms PhyslibExtTest.Chemistry.Uncertainty.powerLaw_density
#print axioms PhyslibExtTest.Chemistry.Uncertainty.densityEstimate_ne_zero
#print axioms PhyslibExtTest.Chemistry.Uncertainty.density_estimate
#print axioms PhyslibExtTest.Chemistry.Uncertainty.density_sensitivities
#print axioms PhyslibExtTest.Chemistry.Uncertainty.density_linearizedVariance
#print axioms PhyslibExtTest.Chemistry.Uncertainty.density_linearizedVariance_twoPoint
#print axioms PhyslibExtTest.Chemistry.Uncertainty.density_relativeUncertainty
#print axioms PhyslibExtTest.Chemistry.Uncertainty.density_logUncertainty
#print axioms PhyslibExtTest.Chemistry.Uncertainty.relativeUncertainty_mul_firstOrder
#print axioms PhyslibExtTest.Chemistry.Uncertainty.relativeUncertainty_div_firstOrder
#print axioms PhyslibExtTest.Chemistry.Uncertainty.relativeUncertainty_zpow_firstOrder
#print axioms PhyslibExtTest.Chemistry.Uncertainty.hasFDerivAt_prodFun
#print axioms PhyslibExtTest.Chemistry.Uncertainty.prodFun'_eq
#print axioms PhyslibExtTest.Chemistry.Uncertainty.hasFDerivAt_prodFun'
#print axioms PhyslibExtTest.Chemistry.Uncertainty.fderiv_prodFun
#print axioms PhyslibExtTest.Chemistry.Uncertainty.contDiff_prodFun
#print axioms PhyslibExtTest.Chemistry.Uncertainty.norm_proj_fin_two_le
#print axioms PhyslibExtTest.Chemistry.Uncertainty.norm_prodFun''_le
#print axioms PhyslibExtTest.Chemistry.Uncertainty.norm_prodStep
#print axioms PhyslibExtTest.Chemistry.Uncertainty.prodPoint_mem_box
#print axioms PhyslibExtTest.Chemistry.Uncertainty.prodPoint_add_prodStep_mem_box
#print axioms PhyslibExtTest.Chemistry.Uncertainty.prodFun_exact_ne_firstOrder
#print axioms PhyslibExtTest.Chemistry.Uncertainty.prodFun_remainder_bound
#print axioms PhyslibExtTest.Chemistry.Uncertainty.prodFun_remainder_bound_of_contDiff
#print axioms PhyslibExtTest.Chemistry.Uncertainty.prodFun_linearizedVariance_twoPoint
#print axioms PhyslibExtTest.Chemistry.Uncertainty.prodFun_linearizedVariance_of_contDiff
#print axioms PhyslibExtTest.Chemistry.Uncertainty.prodFun_linearizedVariance_correlated
#print axioms PhyslibExtTest.Chemistry.Uncertainty.prodFun_exactVariance_twoPoint
#print axioms PhyslibExtTest.Chemistry.Uncertainty.norm_fin_one
#print axioms PhyslibExtTest.Chemistry.Uncertainty.norm_sqFun''_le
#print axioms PhyslibExtTest.Chemistry.Uncertainty.sqFun_remainder_eq
#print axioms PhyslibExtTest.Chemistry.Uncertainty.integral_sampleMean_heads
#print axioms PhyslibExtTest.Chemistry.Uncertainty.variance_heads
#print axioms PhyslibExtTest.Chemistry.Uncertainty.integral_sampleVariance_heads
#print axioms PhyslibExtTest.Chemistry.Uncertainty.integral_sampleVariance_heads_eq_variance
#print axioms PhyslibExtTest.Chemistry.Uncertainty.integral_biasedVariance_heads
#print axioms PhyslibExtTest.Chemistry.Uncertainty.roundSigFig_eq_of_mem
#print axioms PhyslibExtTest.Chemistry.Uncertainty.roundSigFig_one_seven_fifths
#print axioms PhyslibExtTest.Chemistry.Uncertainty.roundSigFig_one_two
#print axioms PhyslibExtTest.Chemistry.Uncertainty.roundSigFig_one_fourteen_fifths
#print axioms PhyslibExtTest.Chemistry.Uncertainty.roundSigFig_counterexample
#print axioms PhyslibExtTest.Chemistry.Uncertainty.roundSigFig_counterexample_exists
#print axioms PhyslibExtTest.Chemistry.Uncertainty.roundSigFig_three
#print axioms PhyslibExtTest.Chemistry.Uncertainty.roundSigFig_two_small
#print axioms PhyslibExtTest.Chemistry.Uncertainty.abs_roundSigFig_three_sub_le
#print axioms PhyslibExtTest.Chemistry.Uncertainty.roundSigFig_wellDefined_three
#print axioms PhyslibExtTest.Chemistry.Uncertainty.roundSigFig_zero_two
#print axioms PhyslibExtTest.Chemistry.Uncertainty.zeroEstimate_hypothesis_fails
#print axioms PhyslibExtTest.Chemistry.Uncertainty.relativeUncertainty_fails_at_zero
#print axioms PhyslibExtTest.Chemistry.Uncertainty.prodFun_linearizedVariance_at_zero

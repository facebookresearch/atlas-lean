/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
public import MathlibExt.MeasureTheory.Function.BoundedMeasurable
public import MathlibExt.MeasureTheory.VectorMeasure.RegularVariation

import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Integrating bounded measurable functions against complex measures

This file defines the pairing of a bounded measurable complex-valued function with a complex
measure.  Every complex measure has finite total variation; the definition uses Mathlib's
vector-measure integral with complex multiplication regarded as a continuous real-bilinear map.

Although the underlying vector integral is only real-bilinear in general, complex multiplication
makes this pairing complex-linear in both the function and the measure.  The corresponding
complex-linearity results are proved explicitly below.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

open MathlibExt.MeasureTheory.Function

namespace MathlibExt.MeasureTheory.VectorMeasure

noncomputable section

universe u

variable {X : Type u} [MeasurableSpace X]

local instance complexIntegralVariationFinite (μ : ComplexMeasure X) :
    IsFiniteMeasure μ.variation :=
  ComplexMeasure.isFiniteMeasure_variation μ

/-- The integral of a bounded measurable function against a complex measure, using complex
multiplication as the real-bilinear pairing in Mathlib's vector-measure integral. -/
noncomputable def complexIntegral (μ : ComplexMeasure X) (φ : BoundedMeasurableFunction X) : ℂ :=
  ∫ᵛ x, φ x ∂[ContinuousLinearMap.mul ℝ ℂ; μ]

/-- A bounded measurable function is integrable with respect to every complex measure. -/
theorem complexIntegral_integrable (μ : ComplexMeasure X) (φ : BoundedMeasurableFunction X) :
    μ.Integrable (fun x ↦ φ x) := by
  apply Integrable.of_bound φ.measurable.aestronglyMeasurable ‖φ‖
  exact Filter.Eventually.of_forall fun x ↦ φ.norm_apply_le_norm x

/-- Integrating the zero bounded measurable function against a complex measure gives zero. -/
@[simp]
theorem complexIntegral_zero (μ : ComplexMeasure X) :
    complexIntegral μ (0 : BoundedMeasurableFunction X) = 0 := by
  simp [complexIntegral]

/-- Integrating against the zero complex measure gives zero. -/
@[simp]
theorem complexIntegral_zero_measure (φ : BoundedMeasurableFunction X) :
    complexIntegral (0 : ComplexMeasure X) φ = 0 := by
  simp [complexIntegral]

/-- Additivity in the bounded measurable function. -/
theorem complexIntegral_add (μ : ComplexMeasure X) (φ ψ : BoundedMeasurableFunction X) :
    complexIntegral μ (φ + ψ) = complexIntegral μ φ + complexIntegral μ ψ := by
  change (∫ᵛ x, φ x + ψ x ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) = _
  exact MeasureTheory.VectorMeasure.integral_fun_add
    (complexIntegral_integrable μ φ) (complexIntegral_integrable μ ψ)

/-- Complex homogeneity in the bounded measurable function.  This uses the generic scalar
linearity theorem for `setToFun`, together with complex-linearity of multiplication in its first
argument; it does not identify complex scalar multiplication with the real scalar API of the
vector integral. -/
theorem complexIntegral_smul (μ : ComplexMeasure X) (c : ℂ)
    (φ : BoundedMeasurableFunction X) :
    complexIntegral μ (c • φ) = c • complexIntegral μ φ := by
  let B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ
  change (∫ᵛ x, c • φ x ∂[B; μ]) = c • ∫ᵛ x, φ x ∂[B; μ]
  rw [MeasureTheory.VectorMeasure.integral_eq_setToFun,
    MeasureTheory.VectorMeasure.integral_eq_setToFun]
  have hline : ∀ d : ℂ, ∀ s z, μ.transpose B s (d • z) = d • μ.transpose B s z := by
    intro d s z
    change (d * z) * μ s = d * (z * μ s)
    rw [mul_assoc]
  convert (setToFun_smul (α := X) (E := ℂ) (F := ℂ) (𝕜 := ℂ)
      (μ := μ.variation) (T := μ.transpose B)
      (dominatedFinMeasAdditive_cbmApplyMeasure μ B) hline c (fun x ↦ φ x)) using 1

/-- Additivity in the complex measure. -/
theorem complexIntegral_add_measure (μ ν : ComplexMeasure X)
    (φ : BoundedMeasurableFunction X) :
    complexIntegral (μ + ν) φ = complexIntegral μ φ + complexIntegral ν φ := by
  exact MeasureTheory.VectorMeasure.integral_add_vectorMeasure
    (complexIntegral_integrable μ φ) (complexIntegral_integrable ν φ)

/-- Multiplying the set-function in a `setToFun` construction by a complex scalar multiplies its
value by the same scalar.  Mathlib provides this directly for real scalars; this local lemma records
the complex consequence needed for complex measures. -/
private theorem setToFun_complex_smul_left
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ : Measure X} {T : Set X → E →L[ℝ] ℂ} {C : ℝ}
    (hT : DominatedFinMeasAdditive ρ T C) (c : ℂ) (f : X → E) :
    setToFun ρ (fun s ↦ c • T s) (hT.smul c) f = c • setToFun ρ T hT f := by
  by_cases hf : Integrable f ρ
  · apply hf.induction (P := fun g ↦
        setToFun ρ (fun s ↦ c • T s) (hT.smul c) g = c • setToFun ρ T hT g)
    · intro d s hs hρs
      rw [setToFun_indicator_const (hT.smul c) hs hρs.ne,
        setToFun_indicator_const hT hs hρs.ne]
      rfl
    · intro g h _ hgi hhi hg hh
      rw [setToFun_add (hT.smul c) hgi hhi, setToFun_add hT hgi hhi, hg, hh, smul_add]
    · exact isClosed_eq (continuous_setToFun (hT.smul c))
        ((continuous_const_smul c).comp (continuous_setToFun hT))
    · intro g h hgh _ hg
      calc
        setToFun ρ (fun s ↦ c • T s) (hT.smul c) h =
            setToFun ρ (fun s ↦ c • T s) (hT.smul c) g :=
          (setToFun_congr_ae (hT.smul c) hgh).symm
        _ = c • setToFun ρ T hT g := hg
        _ = c • setToFun ρ T hT h :=
          congrArg (c • ·) (setToFun_congr_ae hT hgh)
  · rw [setToFun_undef (hT.smul c) hf, setToFun_undef hT hf, smul_zero]

/-- Complex homogeneity in the measure.  The proof uses
`variation (c • μ) = ‖c‖₊ • variation μ` to change the reference measure, then applies the local
complex scalar extension lemma to the transposed set-function. -/
theorem complexIntegral_smul_measure (c : ℂ) (μ : ComplexMeasure X)
    (φ : BoundedMeasurableFunction X) :
    complexIntegral (c • μ) φ = c • complexIntegral μ φ := by
  let B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ
  let T : Set X → ℂ →L[ℝ] ℂ := μ.transpose B
  let T' : Set X → ℂ →L[ℝ] ℂ := fun s ↦ c • T s
  let hT : DominatedFinMeasAdditive μ.variation T ‖B‖ :=
    dominatedFinMeasAdditive_cbmApplyMeasure μ B
  let hT' : DominatedFinMeasAdditive μ.variation T' (‖c‖ * ‖B‖) := hT.smul c
  have htranspose :
      ((c • μ).transpose B : Set X → ℂ →L[ℝ] ℂ) = T' := by
    funext s
    ext z
    change z * (c * μ s) = c * (z * μ s)
    rw [← mul_assoc, ← mul_assoc, mul_comm z c]
  have hT'_smul :
      DominatedFinMeasAdditive (‖c‖₊ • μ.variation) T' ‖B‖ := by
    rw [← MeasureTheory.VectorMeasure.variation_smul]
    rw [← htranspose]
    exact dominatedFinMeasAdditive_cbmApplyMeasure (c • μ) B
  have hT'_c : DominatedFinMeasAdditive (c • μ).variation T' ‖B‖ := by
    rw [← htranspose]
    exact dominatedFinMeasAdditive_cbmApplyMeasure (c • μ) B
  have hvariation₁ : (c • μ).variation ≤ (1 : ℝ≥0∞) • (‖c‖₊ • μ.variation) := by
    simpa only [one_smul, MeasureTheory.VectorMeasure.variation_smul] using
      (le_rfl : ‖c‖₊ • μ.variation ≤ ‖c‖₊ • μ.variation)
  have hvariation₂ : ‖c‖₊ • μ.variation ≤ (1 : ℝ≥0∞) • (c • μ).variation := by
    simpa only [one_smul, MeasureTheory.VectorMeasure.variation_smul] using
      (le_rfl : ‖c‖₊ • μ.variation ≤ ‖c‖₊ • μ.variation)
  unfold complexIntegral
  rw [MeasureTheory.VectorMeasure.integral_eq_setToFun,
    MeasureTheory.VectorMeasure.integral_eq_setToFun]
  calc
    setToFun (c • μ).variation ((c • μ).transpose B)
        (dominatedFinMeasAdditive_cbmApplyMeasure (c • μ) B) (fun x ↦ φ x) =
        setToFun (c • μ).variation T' hT'_c (fun x ↦ φ x) := by
      apply setToFun_congr_left
      exact htranspose
    _ = setToFun (‖c‖₊ • μ.variation) T' hT'_smul (fun x ↦ φ x) :=
      setToFun_congr_measure 1 1 (by simp) (by simp) hvariation₁ hvariation₂
        hT'_c hT'_smul (fun x ↦ φ x)
    _ = setToFun μ.variation T' hT' (fun x ↦ φ x) :=
      (setToFun_congr_smul_measure' ‖c‖₊ hT' hT'_smul (fun x ↦ φ x)).symm
    _ = c • setToFun μ.variation T hT (fun x ↦ φ x) :=
      setToFun_complex_smul_left hT c (fun x ↦ φ x)
    _ = c • setToFun μ.variation (μ.transpose B)
        (dominatedFinMeasAdditive_cbmApplyMeasure μ B) (fun x ↦ φ x) := rfl

/-- The sharp total-variation bound for the complex integral pairing. -/
theorem norm_complexIntegral_le (μ : ComplexMeasure X) (φ : BoundedMeasurableFunction X) :
    ‖complexIntegral μ φ‖ ≤ ‖φ‖ * μ.variation.real univ := by
  simpa [complexIntegral, ContinuousLinearMap.opNorm_mul] using
    (MeasureTheory.VectorMeasure.norm_integral_le_of_norm_le_const
      (μ := μ) (B := ContinuousLinearMap.mul ℝ ℂ)
      (f := fun x ↦ φ x)
      (Filter.Eventually.of_forall fun x ↦ φ.norm_apply_le_norm x))

/-- Evaluation on a constant-valued measurable indicator. -/
theorem complexIntegral_indicatorConst (μ : ComplexMeasure X)
    (s : Set X) (hs : MeasurableSet s) (c : ℂ) :
    complexIntegral μ (BoundedMeasurableFunction.indicatorConst s hs c) = c * μ s := by
  simpa [complexIntegral, BoundedMeasurableFunction.indicatorConst_apply] using
    (MeasureTheory.VectorMeasure.integral_indicator_const
      (μ := μ) (B := ContinuousLinearMap.mul ℝ ℂ) c hs)

/-- Evaluation on a measurable characteristic function. -/
theorem complexIntegral_indicator (μ : ComplexMeasure X) (s : Set X) (hs : MeasurableSet s) :
    complexIntegral μ (BoundedMeasurableFunction.indicator s hs) = μ s := by
  simpa [BoundedMeasurableFunction.indicator] using
    complexIntegral_indicatorConst μ s hs (1 : ℂ)

/-- The finite sum formula for a measurable simple function. -/
theorem complexIntegral_ofSimpleFunc (μ : ComplexMeasure X) (f : SimpleFunc X ℂ) :
    complexIntegral μ (BoundedMeasurableFunction.ofSimpleFunc f) =
      ∑ c ∈ f.range, c * μ (f ⁻¹' {c}) := by
  have hf : μ.Integrable (fun x ↦ f x) := by
    simpa only [BoundedMeasurableFunction.ofSimpleFunc_apply] using
      complexIntegral_integrable μ (BoundedMeasurableFunction.ofSimpleFunc f)
  change (∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) = _
  rw [MeasureTheory.VectorMeasure.integral_eq_setToFun]
  simpa [BoundedMeasurableFunction.ofSimpleFunc_apply,
    transpose_eq_cbmApplyMeasure, cbmApplyMeasure_apply,
    ContinuousLinearMap.mul_apply'] using
    (setToFun_simpleFunc (dominatedFinMeasAdditive_cbmApplyMeasure μ
      (ContinuousLinearMap.mul ℝ ℂ)) f hf)

/-- The complex integral against a scalar Dirac measure is the scalar times pointwise evaluation. -/
@[simp]
theorem complexIntegral_dirac (a : X) (z : ℂ) (φ : BoundedMeasurableFunction X) :
    complexIntegral (MeasureTheory.VectorMeasure.dirac a z) φ = φ a * z := by
  simpa [complexIntegral] using
    (MeasureTheory.VectorMeasure.integral_dirac'
      (B := ContinuousLinearMap.mul ℝ ℂ)
      (f := fun x ↦ φ x) φ.measurable.stronglyMeasurable)

/-- Pointwise equal bounded measurable functions have equal complex integrals. -/
theorem complexIntegral_congr_fun (μ : ComplexMeasure X)
    {φ ψ : BoundedMeasurableFunction X} (h : ∀ x, φ x = ψ x) :
    complexIntegral μ φ = complexIntegral μ ψ := by
  apply MeasureTheory.VectorMeasure.integral_congr_ae
  exact Filter.Eventually.of_forall h

/-- Almost-everywhere equal bounded measurable functions have equal complex integrals. -/
theorem complexIntegral_congr_ae (μ : ComplexMeasure X)
    {φ ψ : BoundedMeasurableFunction X} (h : (fun x ↦ φ x) =ᵐ[μ.variation] fun x ↦ ψ x) :
    complexIntegral μ φ = complexIntegral μ ψ :=
  MeasureTheory.VectorMeasure.integral_congr_ae h

/-- For a fixed complex measure, integration is a continuous complex-linear functional on bounded
measurable functions. -/
noncomputable def complexIntegralCLM (μ : ComplexMeasure X) :
    BoundedMeasurableFunction X →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := complexIntegral μ
      map_add' := complexIntegral_add μ
      map_smul' := complexIntegral_smul μ }
    (μ.variation.real univ)
    (fun φ ↦ by
      simpa [mul_comm] using norm_complexIntegral_le μ φ)

/-- The continuous linear complex-integral map evaluates by the original complex integral. -/
@[simp]
theorem complexIntegralCLM_apply (μ : ComplexMeasure X) (φ : BoundedMeasurableFunction X) :
    complexIntegralCLM μ φ = complexIntegral μ φ :=
  rfl

end

end MathlibExt.MeasureTheory.VectorMeasure

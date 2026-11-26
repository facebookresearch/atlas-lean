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
# Bounded measurable integration against complex measures

On any measurable space, a bounded measurable complex function is integrable against every
complex measure. The pairing `I_μ(f)=∫ f dμ` is complex-linear in both `f` and `μ`, and
satisfies `|I_μ(f)|≤‖f‖∞ |μ|(X)`.

For indicators, `I_μ(c1_s)=c μ(s)`, and for a measurable simple function it is the finite sum
`Σ_c∈range(f) c μ(f⁻¹({c}))`. Pointwise equality or equality almost everywhere for total
variation gives equal integrals. For fixed `μ`, this is a bounded complex-linear functional on
pointwise bounded measurable functions.
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

/-- **Integral pairing of a bounded measurable function and complex measure.** Let `X` be a
measurable space, `μ : ComplexMeasure X` and `f : X → ℂ` bounded measurable with pointwise
supremum norm. Write `I_μ(f)=∫ f dμ`; the total variation `|μ|` is finite.
`complexIntegral μ f=I_μ(f)` is the vector-measure integral paired by complex
multiplication, giving the ordinary complex integral. -/
noncomputable def complexIntegral (μ : ComplexMeasure X) (φ : BoundedMeasurableFunction X) : ℂ :=
  ∫ᵛ x, φ x ∂[ContinuousLinearMap.mul ℝ ℂ; μ]

/-- **Bounded measurable functions integrable against complex measures.** Let `X` be a
measurable space, `μ : ComplexMeasure X` and `f : X → ℂ` bounded measurable with pointwise
supremum norm. Write `I_μ(f)=∫ f dμ`; the total variation `|μ|` is finite. the underlying
function `f` is integrable against `μ` because it is bounded and `|μ|(X)<∞`. -/
theorem complexIntegral_integrable (μ : ComplexMeasure X) (φ : BoundedMeasurableFunction X) :
    μ.Integrable (fun x ↦ φ x) := by
  apply Integrable.of_bound φ.measurable.aestronglyMeasurable ‖φ‖
  exact Filter.Eventually.of_forall fun x ↦ φ.norm_apply_le_norm x

/-- **Zero function has zero complex integral.** Let `X` be a measurable space, `μ :
ComplexMeasure X` and `f : X → ℂ` bounded measurable with pointwise supremum norm. Write
`I_μ(f)=∫ f dμ`; the total variation `|μ|` is finite. `I_μ(0)=0`. -/
@[simp]
theorem complexIntegral_zero (μ : ComplexMeasure X) :
    complexIntegral μ (0 : BoundedMeasurableFunction X) = 0 := by
  simp [complexIntegral]

/-- **Zero complex measure has zero integral.** Let `X` be a measurable space, `μ :
ComplexMeasure X` and `f : X → ℂ` bounded measurable with pointwise supremum norm. Write
`I_μ(f)=∫ f dμ`; the total variation `|μ|` is finite. `I_0(f)=0`. -/
@[simp]
theorem complexIntegral_zero_measure (φ : BoundedMeasurableFunction X) :
    complexIntegral (0 : ComplexMeasure X) φ = 0 := by
  simp [complexIntegral]

/-- **Additivity of the bounded complex integrand.** Let `X` be a measurable space, `μ :
ComplexMeasure X` and `f : X → ℂ` bounded measurable with pointwise supremum norm. Write
`I_μ(f)=∫ f dμ`; the total variation `|μ|` is finite. for another bounded measurable `g`,
`I_μ(f+g)=I_μ(f)+I_μ(g)`. -/
theorem complexIntegral_add (μ : ComplexMeasure X) (φ ψ : BoundedMeasurableFunction X) :
    complexIntegral μ (φ + ψ) = complexIntegral μ φ + complexIntegral μ ψ := by
  change (∫ᵛ x, φ x + ψ x ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) = _
  exact MeasureTheory.VectorMeasure.integral_fun_add
    (complexIntegral_integrable μ φ) (complexIntegral_integrable μ ψ)

/-- **Complex homogeneity of the bounded integrand.** Let `X` be a measurable space, `μ :
ComplexMeasure X` and `f : X → ℂ` bounded measurable with pointwise supremum norm. Write
`I_μ(f)=∫ f dμ`; the total variation `|μ|` is finite. for `z∈ℂ`, `I_μ(z • f)=z • I_μ(f)`. -/
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

/-- **Additivity in the complex measure.** Let `X` be a measurable space, `μ : ComplexMeasure
X` and `f : X → ℂ` bounded measurable with pointwise supremum norm. Write `I_μ(f)=∫ f dμ`;
the total variation `|μ|` is finite. for another complex measure `ν`,
`I_(μ+ν)(f)=I_μ(f)+I_ν(f)`. -/
theorem complexIntegral_add_measure (μ ν : ComplexMeasure X)
    (φ : BoundedMeasurableFunction X) :
    complexIntegral (μ + ν) φ = complexIntegral μ φ + complexIntegral ν φ := by
  exact MeasureTheory.VectorMeasure.integral_add_vectorMeasure
    (complexIntegral_integrable μ φ) (complexIntegral_integrable ν φ)

/-- **Complex scaling of a dominated finitely additive integral.** Let `X` be measurable, `E`
a real normed space, `ρ` a measure and `T_s : E →L[ℝ] ℂ` a set-indexed family satisfying
`DominatedFinMeasAdditive ρ T C`. For `z∈ℂ` and any function `f : X → E`, the totalized
integral construction satisfies `setToFun ρ (z • T) f=z • setToFun ρ T f`. -/
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

/-- **Complex homogeneity in the measure.** Let `X` be a measurable space, `μ : ComplexMeasure
X` and `f : X → ℂ` bounded measurable with pointwise supremum norm. Write `I_μ(f)=∫ f dμ`;
the total variation `|μ|` is finite. for `z∈ℂ`, `I_(z • μ)(f)=z • I_μ(f)`. -/
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

/-- **Total-variation norm bound for a bounded complex integral.** Let `X` be a measurable
space, `μ : ComplexMeasure X` and `f : X → ℂ` bounded measurable with pointwise supremum
norm. Write `I_μ(f)=∫ f dμ`; the total variation `|μ|` is finite.
`|I_μ(f)|≤‖f‖∞*|μ|.real(X)`. -/
theorem norm_complexIntegral_le (μ : ComplexMeasure X) (φ : BoundedMeasurableFunction X) :
    ‖complexIntegral μ φ‖ ≤ ‖φ‖ * μ.variation.real univ := by
  simpa [complexIntegral, ContinuousLinearMap.opNorm_mul] using
    (MeasureTheory.VectorMeasure.norm_integral_le_of_norm_le_const
      (μ := μ) (B := ContinuousLinearMap.mul ℝ ℂ)
      (f := fun x ↦ φ x)
      (Filter.Eventually.of_forall fun x ↦ φ.norm_apply_le_norm x))

/-- **Complex integral of a scalar measurable indicator.** Let `X` be a measurable space, `μ :
ComplexMeasure X` and `f : X → ℂ` bounded measurable with pointwise supremum norm. Write
`I_μ(f)=∫ f dμ`; the total variation `|μ|` is finite. for measurable `s⊆X` and `z∈ℂ`,
`I_μ(z1_s)=z*μ(s)`. -/
theorem complexIntegral_indicatorConst (μ : ComplexMeasure X)
    (s : Set X) (hs : MeasurableSet s) (c : ℂ) :
    complexIntegral μ (BoundedMeasurableFunction.indicatorConst s hs c) = c * μ s := by
  simpa [complexIntegral, BoundedMeasurableFunction.indicatorConst_apply] using
    (MeasureTheory.VectorMeasure.integral_indicator_const
      (μ := μ) (B := ContinuousLinearMap.mul ℝ ℂ) c hs)

/-- **Complex integral of a characteristic function.** Let `X` be a measurable space, `μ :
ComplexMeasure X` and `f : X → ℂ` bounded measurable with pointwise supremum norm. Write
`I_μ(f)=∫ f dμ`; the total variation `|μ|` is finite. for measurable `s⊆X`,
`I_μ(1_s)=μ(s)`. -/
theorem complexIntegral_indicator (μ : ComplexMeasure X) (s : Set X) (hs : MeasurableSet s) :
    complexIntegral μ (BoundedMeasurableFunction.indicator s hs) = μ s := by
  simpa [BoundedMeasurableFunction.indicator] using
    complexIntegral_indicatorConst μ s hs (1 : ℂ)

/-- **Finite sum formula for a measurable simple integrand.** Let `X` be a measurable space,
`μ : ComplexMeasure X` and `f : X → ℂ` bounded measurable with pointwise supremum norm.
Write `I_μ(f)=∫ f dμ`; the total variation `|μ|` is finite. for a measurable simple
function `g`, `I_μ(g)=Σ_z∈range(g) z*μ(g⁻¹({z}))`. -/
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

/-- **Integral against a scalar point-mass measure.** Let `X` be a measurable space, `μ :
ComplexMeasure X` and `f : X → ℂ` bounded measurable with pointwise supremum norm. Write
`I_μ(f)=∫ f dμ`; the total variation `|μ|` is finite. for `a∈X`, `z∈ℂ`,
`I_(zδ_a)(f)=f(a)*z`. The vector-measure point mass is defined without a
measurable-singleton assumption. -/
@[simp]
theorem complexIntegral_dirac (a : X) (z : ℂ) (φ : BoundedMeasurableFunction X) :
    complexIntegral (MeasureTheory.VectorMeasure.dirac a z) φ = φ a * z := by
  simpa [complexIntegral] using
    (MeasureTheory.VectorMeasure.integral_dirac'
      (B := ContinuousLinearMap.mul ℝ ℂ)
      (f := fun x ↦ φ x) φ.measurable.stronglyMeasurable)

/-- **Pointwise equality preserves bounded complex integrals.** Let `X` be a measurable space,
`μ : ComplexMeasure X` and `f : X → ℂ` bounded measurable with pointwise supremum norm.
Write `I_μ(f)=∫ f dμ`; the total variation `|μ|` is finite. if bounded measurable
functions `f,g` agree at every point, then `I_μ(f)=I_μ(g)`. -/
theorem complexIntegral_congr_fun (μ : ComplexMeasure X)
    {φ ψ : BoundedMeasurableFunction X} (h : ∀ x, φ x = ψ x) :
    complexIntegral μ φ = complexIntegral μ ψ := by
  apply MeasureTheory.VectorMeasure.integral_congr_ae
  exact Filter.Eventually.of_forall h

/-- **Total-variation almost-everywhere equality preserves complex integrals.** Let `X` be a
measurable space, `μ : ComplexMeasure X` and `f : X → ℂ` bounded measurable with pointwise
supremum norm. Write `I_μ(f)=∫ f dμ`; the total variation `|μ|` is finite. if bounded
measurable `f,g` agree almost everywhere for `|μ|`, then `I_μ(f)=I_μ(g)`. -/
theorem complexIntegral_congr_ae (μ : ComplexMeasure X)
    {φ ψ : BoundedMeasurableFunction X} (h : (fun x ↦ φ x) =ᵐ[μ.variation] fun x ↦ ψ x) :
    complexIntegral μ φ = complexIntegral μ ψ :=
  MeasureTheory.VectorMeasure.integral_congr_ae h

/-- **Bounded linear integral functional on measurable bounded functions.** Let `X` be a
measurable space, `μ : ComplexMeasure X` and `f : X → ℂ` bounded measurable with pointwise
supremum norm. Write `I_μ(f)=∫ f dμ`; the total variation `|μ|` is finite.
`complexIntegralCLM μ : BoundedMeasurableFunction X →L[ℂ] ℂ` sends `f` to `I_μ(f)`, with
bound `|I_μ(f)|≤|μ|.real(X)‖f‖∞`. -/
noncomputable def complexIntegralCLM (μ : ComplexMeasure X) :
    BoundedMeasurableFunction X →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := complexIntegral μ
      map_add' := complexIntegral_add μ
      map_smul' := complexIntegral_smul μ }
    (μ.variation.real univ)
    (fun φ ↦ by
      simpa [mul_comm] using norm_complexIntegral_le μ φ)

/-- **Value of the bounded complex integral functional.** Let `X` be a measurable space, `μ :
ComplexMeasure X` and `f : X → ℂ` bounded measurable with pointwise supremum norm. Write
`I_μ(f)=∫ f dμ`; the total variation `|μ|` is finite. `complexIntegralCLM μ
f=complexIntegral μ f=I_μ(f)`. -/
@[simp]
theorem complexIntegralCLM_apply (μ : ComplexMeasure X) (φ : BoundedMeasurableFunction X) :
    complexIntegralCLM μ φ = complexIntegral μ φ :=
  rfl

end

end MathlibExt.MeasureTheory.VectorMeasure

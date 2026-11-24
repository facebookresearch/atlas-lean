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

public import MathlibExt.MeasureTheory.Integral.RieszMarkovKakutani.SignedReal
public import MathlibExt.MeasureTheory.Function.BoundedMeasurable.Continuous
public import MathlibExt.MeasureTheory.VectorMeasure.ComplexIntegral
public import Mathlib.Analysis.RCLike.ContinuousMap

/-!
# Complex Riesz--Markov representation on compact spaces

On a compact Hausdorff Borel space, bounded complex-linear functionals on
`C(X, ℂ)` correspond to complex measures with regular total variation.  The
inverse is obtained by applying the signed real Riesz--Markov equivalence to
the real and imaginary restrictions of a complex functional.

The carrier in this file is norm-free and installs no global instance on
complex measures.  This layer records the total-variation upper bound.  The
reverse norm inequality, which requires a finite-phase approximation followed
by regular `L¹` density and radial clipping, is not claimed here.
-/

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

open MathlibExt.MeasureTheory.Function
open MathlibExt.MeasureTheory.VectorMeasure

namespace MathlibExt.MeasureTheory

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X] [R1Space X]
  [MeasurableSpace X] [BorelSpace X]

/-- Complex measures whose total variation is regular. -/
noncomputable def regularComplexMeasureSubmodule (X : Type u)
    [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X] :
    Submodule ℂ (ComplexMeasure X) where
  carrier := {mu | VectorMeasure.HasRegularVariation mu}
  zero_mem' := VectorMeasure.HasRegularVariation.zero
  add_mem' := by
    intro mu nu hmu hnu
    exact ComplexMeasure.HasRegularVariation.add hmu hnu
  smul_mem' := by
    intro c mu hmu
    exact ComplexMeasure.HasRegularVariation.smul hmu c

/-- A complex measure with regular total variation. -/
abbrev RegularComplexMeasure (X : Type u) [TopologicalSpace X] [R1Space X]
    [MeasurableSpace X] [BorelSpace X] :=
  ↑(regularComplexMeasureSubmodule X)

namespace RegularComplexMeasure

/-- The defining regularity property. -/
theorem variation_regular (mu : RegularComplexMeasure X) :
    (mu : ComplexMeasure X).variation.Regular :=
  mu.property

/-- The real signed component of a regular complex measure. -/
noncomputable def re (mu : RegularComplexMeasure X) : RegularSignedMeasure X := by
  have hre : VectorMeasure.HasRegularVariation (mu : ComplexMeasure X).re :=
    (ComplexMeasure.hasRegularVariation_iff_re_im (mu : ComplexMeasure X)).mp mu.property |>.1
  refine ⟨(mu : ComplexMeasure X).re, ?_⟩
  change ((mu : ComplexMeasure X).re).totalVariation.Regular
  rw [SignedMeasure.totalVariation_eq_variation]
  exact hre

/-- The imaginary signed component of a regular complex measure. -/
noncomputable def im (mu : RegularComplexMeasure X) : RegularSignedMeasure X := by
  have him : VectorMeasure.HasRegularVariation (mu : ComplexMeasure X).im :=
    (ComplexMeasure.hasRegularVariation_iff_re_im (mu : ComplexMeasure X)).mp mu.property |>.2
  refine ⟨(mu : ComplexMeasure X).im, ?_⟩
  change ((mu : ComplexMeasure X).im).totalVariation.Regular
  rw [SignedMeasure.totalVariation_eq_variation]
  exact him

/-- The regular signed real component has the real part of the underlying complex measure. -/
@[simp]
theorem coe_re (mu : RegularComplexMeasure X) :
    ((RegularComplexMeasure.re mu : RegularSignedMeasure X) : SignedMeasure X) =
      (mu : ComplexMeasure X).re := rfl

/-- The regular signed imaginary component has the imaginary part of the underlying complex measure. -/
@[simp]
theorem coe_im (mu : RegularComplexMeasure X) :
    ((RegularComplexMeasure.im mu : RegularSignedMeasure X) : SignedMeasure X) =
      (mu : ComplexMeasure X).im := rfl

end RegularComplexMeasure

variable [CompactSpace X] [T2Space X]

/-- The real-linear pointwise inclusion of continuous real functions into continuous complex functions. -/
@[no_expose]
noncomputable def realContinuousMapCLM : C(X, ℝ) →L[ℝ] C(X, ℂ) :=
  Complex.ofRealCLM.compLeftContinuous ℝ X

private def continuousMapRealPart (f : C(X, ℂ)) : C(X, ℝ) :=
  (Complex.reCLM.compLeftContinuous ℝ X) f

private def continuousMapImaginaryPart (f : C(X, ℂ)) : C(X, ℝ) :=
  (Complex.imCLM.compLeftContinuous ℝ X) f

omit [R1Space X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [T2Space X] in
/-- The real-to-complex continuous-map inclusion evaluates by the original real scalar inclusion. -/
@[simp]
theorem realContinuousMapCLM_apply (f : C(X, ℝ)) (x : X) :
    realContinuousMapCLM f x = (f x : ℂ) := by
  unfold realContinuousMapCLM
  rfl

omit [R1Space X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [T2Space X] in
@[simp]
private theorem continuousMapRealPart_apply (f : C(X, ℂ)) (x : X) :
    continuousMapRealPart f x = (f x).re := rfl

omit [R1Space X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [T2Space X] in
@[simp]
private theorem continuousMapImaginaryPart_apply (f : C(X, ℂ)) (x : X) :
    continuousMapImaginaryPart f x = (f x).im := rfl

omit [R1Space X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [T2Space X] in
private theorem real_imaginary_decomposition (f : C(X, ℂ)) :
    realContinuousMapCLM (continuousMapRealPart f) +
        Complex.I • realContinuousMapCLM (continuousMapImaginaryPart f) = f := by
  ext x
  simpa [smul_eq_mul, mul_comm] using Complex.re_add_im (f x)

/-- Real part of a complex functional restricted to the real-valued continuous
functions. -/
noncomputable def complexDualRealRestriction (Λ : StrongDual ℂ C(X, ℂ)) :
    StrongDual ℝ C(X, ℝ) :=
  Complex.reCLM.comp ((Λ.restrictScalars ℝ).comp realContinuousMapCLM)

/-- Imaginary part of a complex functional restricted to the real-valued
continuous functions. -/
noncomputable def complexDualImagRestriction (Λ : StrongDual ℂ C(X, ℂ)) :
    StrongDual ℝ C(X, ℝ) :=
  Complex.imCLM.comp ((Λ.restrictScalars ℝ).comp realContinuousMapCLM)

omit [R1Space X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [T2Space X] in
/-- The real restriction evaluates by taking the real part of the functional on the complexified function. -/
@[simp]
theorem complexDualRealRestriction_apply
    (Λ : StrongDual ℂ C(X, ℂ)) (f : C(X, ℝ)) :
    complexDualRealRestriction Λ f = (Λ (realContinuousMapCLM f)).re := rfl

omit [R1Space X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [T2Space X] in
/-- The imaginary restriction evaluates by taking the imaginary part of the functional on the
complexified function. -/
@[simp]
theorem complexDualImagRestriction_apply
    (Λ : StrongDual ℂ C(X, ℂ)) (f : C(X, ℝ)) :
    complexDualImagRestriction Λ f = (Λ (realContinuousMapCLM f)).im := rfl

omit [R1Space X] [MeasurableSpace X] [BorelSpace X] [T2Space X] in
/-- The real restriction has operator norm at most the original complex functional's norm. -/
theorem norm_complexDualRealRestriction_le (Λ : StrongDual ℂ C(X, ℂ)) :
    ‖complexDualRealRestriction Λ‖ ≤ ‖Λ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Λ)
  intro f
  calc
    ‖complexDualRealRestriction Λ f‖ = |(Λ (realContinuousMapCLM f)).re| := by
      rw [complexDualRealRestriction_apply, Real.norm_eq_abs]
    _ ≤ ‖Λ (realContinuousMapCLM f)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖Λ‖ * ‖realContinuousMapCLM f‖ := Λ.le_opNorm _
    _ = ‖Λ‖ * ‖f‖ := by
      congr 1
      rw [ContinuousMap.norm_eq_iSup_norm, ContinuousMap.norm_eq_iSup_norm]
      congr with x
      exact Complex.norm_real (f x)

omit [R1Space X] [MeasurableSpace X] [BorelSpace X] [T2Space X] in
/-- The imaginary restriction has operator norm at most the original complex functional's norm. -/
theorem norm_complexDualImagRestriction_le (Λ : StrongDual ℂ C(X, ℂ)) :
    ‖complexDualImagRestriction Λ‖ ≤ ‖Λ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Λ)
  intro f
  calc
    ‖complexDualImagRestriction Λ f‖ = |(Λ (realContinuousMapCLM f)).im| := by
      rw [complexDualImagRestriction_apply, Real.norm_eq_abs]
    _ ≤ ‖Λ (realContinuousMapCLM f)‖ := Complex.abs_im_le_norm _
    _ ≤ ‖Λ‖ * ‖realContinuousMapCLM f‖ := Λ.le_opNorm _
    _ = ‖Λ‖ * ‖f‖ := by
      congr 1
      rw [ContinuousMap.norm_eq_iSup_norm, ContinuousMap.norm_eq_iSup_norm]
      congr with x
      exact Complex.norm_real (f x)

omit [R1Space X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [T2Space X] in
private theorem complexDual_eq_of_restrictions_eq
    {Λ Γ : StrongDual ℂ C(X, ℂ)}
    (hre : complexDualRealRestriction Λ = complexDualRealRestriction Γ)
    (him : complexDualImagRestriction Λ = complexDualImagRestriction Γ) :
    Λ = Γ := by
  apply ContinuousLinearMap.ext
  intro f
  have honreal (g : C(X, ℝ)) : Λ (realContinuousMapCLM g) = Γ (realContinuousMapCLM g) := by
    apply Complex.ext
    · simpa only [complexDualRealRestriction_apply] using
        congrArg (fun L : StrongDual ℝ C(X, ℝ) ↦ L g) hre
    · simpa only [complexDualImagRestriction_apply] using
        congrArg (fun L : StrongDual ℝ C(X, ℝ) ↦ L g) him
  calc
    Λ f = Λ (realContinuousMapCLM (continuousMapRealPart f) +
        Complex.I • realContinuousMapCLM (continuousMapImaginaryPart f)) := by
      rw [real_imaginary_decomposition]
    _ = Λ (realContinuousMapCLM (continuousMapRealPart f)) +
        Complex.I • Λ (realContinuousMapCLM (continuousMapImaginaryPart f)) := by
      rw [map_add, map_smul]
    _ = Γ (realContinuousMapCLM (continuousMapRealPart f)) +
        Complex.I • Γ (realContinuousMapCLM (continuousMapImaginaryPart f)) := by
      rw [honreal, honreal]
    _ = Γ (realContinuousMapCLM (continuousMapRealPart f) +
        Complex.I • realContinuousMapCLM (continuousMapImaginaryPart f)) := by
      rw [map_add, map_smul]
    _ = Γ f := by rw [real_imaginary_decomposition]

omit [TopologicalSpace X] [R1Space X] [BorelSpace X] [CompactSpace X] [T2Space X] in
private theorem signedVariationFinite (s : SignedMeasure X) : IsFiniteMeasure s.variation := by
  rw [← SignedMeasure.totalVariation_eq_variation]
  infer_instance

omit [TopologicalSpace X] [R1Space X] [BorelSpace X] [CompactSpace X] [T2Space X] in
private theorem boundedMeasurable_integrable_signed
    (s : SignedMeasure X) (phi : BoundedMeasurableFunction X) :
    s.Integrable fun x ↦ phi x := by
  let : IsFiniteMeasure s.variation := signedVariationFinite s
  apply Integrable.of_bound phi.measurable.aestronglyMeasurable ‖phi‖
  exact Filter.Eventually.of_forall fun x ↦ phi.norm_apply_le_norm x

omit [CompactSpace X] [T2Space X] in
private noncomputable def signedComplexIntegral
    (s : SignedMeasure X) (phi : BoundedMeasurableFunction X) : ℂ :=
  ∫ᵛ x, phi x ∂<•s

omit [TopologicalSpace X] [R1Space X] [BorelSpace X] [CompactSpace X] [T2Space X] in
private theorem signedComplexIntegral_add
    (s : SignedMeasure X) (phi psi : BoundedMeasurableFunction X) :
    signedComplexIntegral s (phi + psi) =
      signedComplexIntegral s phi + signedComplexIntegral s psi := by
  simpa [signedComplexIntegral] using
    (VectorMeasure.integral_fun_add
      (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
      (boundedMeasurable_integrable_signed s phi)
      (boundedMeasurable_integrable_signed s psi))

omit [TopologicalSpace X] [R1Space X] [BorelSpace X] [CompactSpace X] [T2Space X] in
private theorem signedComplexIntegral_smul
    (s : SignedMeasure X) (c : ℂ) (phi : BoundedMeasurableFunction X) :
    signedComplexIntegral s (c • phi) = c • signedComplexIntegral s phi := by
  let B : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := (ContinuousLinearMap.lsmul ℝ ℝ).flip
  change (∫ᵛ x, c • phi x ∂[B; s]) = c • ∫ᵛ x, phi x ∂[B; s]
  rw [VectorMeasure.integral_eq_setToFun, VectorMeasure.integral_eq_setToFun]
  have hline : ∀ d : ℂ, ∀ A z, s.transpose B A (d • z) = d • s.transpose B A z := by
    intro d A z
    change (s A : ℝ) • (d * z) = d * ((s A : ℝ) • z)
    simp [mul_left_comm]
  convert (setToFun_smul (α := X) (E := ℂ) (F := ℂ) (𝕜 := ℂ)
      (μ := s.variation) (T := s.transpose B)
      (dominatedFinMeasAdditive_cbmApplyMeasure s B) hline c (fun x ↦ phi x)) using 1

omit [TopologicalSpace X] [R1Space X] [BorelSpace X] [CompactSpace X] [T2Space X] in
private theorem norm_signedComplexIntegral_le
    (s : SignedMeasure X) (phi : BoundedMeasurableFunction X) :
    ‖signedComplexIntegral s phi‖ ≤ ‖phi‖ * s.totalVariation.real univ := by
  let _ : IsFiniteMeasure s.variation := signedVariationFinite s
  have h := VectorMeasure.norm_integral_le_of_norm_le_const
    (μ := s) (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
    (f := fun x ↦ phi x)
    (Filter.Eventually.of_forall fun x ↦ phi.norm_apply_le_norm x)
  simpa [signedComplexIntegral, SignedMeasure.totalVariation_eq_variation] using h

omit [CompactSpace X] [T2Space X] in
private noncomputable def signedComplexIntegralCLM (s : SignedMeasure X) :
    BoundedMeasurableFunction X →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := signedComplexIntegral s
      map_add' := signedComplexIntegral_add s
      map_smul' := signedComplexIntegral_smul s }
    (s.totalVariation.real univ)
    (fun phi ↦ by simpa [mul_comm] using norm_signedComplexIntegral_le s phi)

omit [TopologicalSpace X] [R1Space X] [BorelSpace X] [CompactSpace X] [T2Space X] in
@[simp]
private theorem signedComplexIntegralCLM_apply
    (s : SignedMeasure X) (phi : BoundedMeasurableFunction X) :
    signedComplexIntegralCLM s phi = signedComplexIntegral s phi := rfl

omit [TopologicalSpace X] [R1Space X] [BorelSpace X] [CompactSpace X] [T2Space X] in
private theorem signedComplexIntegral_indicatorConst
    (s : SignedMeasure X) (A : Set X) (hA : MeasurableSet A) (c : ℂ) :
    signedComplexIntegral s (BoundedMeasurableFunction.indicatorConst A hA c) =
      c * (s A : ℂ) := by
  let _ : IsFiniteMeasure s.variation := signedVariationFinite s
  simpa [signedComplexIntegral, BoundedMeasurableFunction.indicatorConst_apply,
    smul_eq_mul, mul_comm] using
      (VectorMeasure.integral_indicator_const
        (μ := s) (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip) c hA)

omit [CompactSpace X] [T2Space X] in
private noncomputable def complexMeasureComponentCLM (mu : ComplexMeasure X) :
    BoundedMeasurableFunction X →L[ℂ] ℂ :=
  signedComplexIntegralCLM mu.re + Complex.I • signedComplexIntegralCLM mu.im

omit [TopologicalSpace X] [R1Space X] [BorelSpace X] [CompactSpace X] [T2Space X] in
@[simp]
private theorem complexMeasureComponentCLM_apply
    (mu : ComplexMeasure X) (phi : BoundedMeasurableFunction X) :
    complexMeasureComponentCLM mu phi =
      signedComplexIntegral mu.re phi + Complex.I * signedComplexIntegral mu.im phi := by
  rfl

omit [TopologicalSpace X] [R1Space X] [BorelSpace X] [CompactSpace X] [T2Space X] in
private theorem ofSimpleFunc_add (f g : SimpleFunc X ℂ) :
    BoundedMeasurableFunction.ofSimpleFunc (f + g) =
      BoundedMeasurableFunction.ofSimpleFunc f + BoundedMeasurableFunction.ofSimpleFunc g := by
  apply Subtype.ext
  apply lp.ext
  funext x
  rfl

omit [TopologicalSpace X] [R1Space X] [BorelSpace X] [CompactSpace X] [T2Space X] in
private theorem complexIntegral_eq_component_on_simple
    (mu : ComplexMeasure X) (f : SimpleFunc X ℂ) :
    complexIntegral mu (BoundedMeasurableFunction.ofSimpleFunc f) =
      complexMeasureComponentCLM mu (BoundedMeasurableFunction.ofSimpleFunc f) := by
  let : IsFiniteMeasure mu.variation := ComplexMeasure.isFiniteMeasure_variation mu
  refine SimpleFunc.induction (motive := fun f ↦
    complexIntegral mu (BoundedMeasurableFunction.ofSimpleFunc f) =
      complexMeasureComponentCLM mu (BoundedMeasurableFunction.ofSimpleFunc f)) ?_ ?_ f
  · intro c A hA
    have hfun : BoundedMeasurableFunction.ofSimpleFunc
        (SimpleFunc.piecewise A hA (SimpleFunc.const X c) (SimpleFunc.const X 0)) =
        BoundedMeasurableFunction.indicatorConst A hA c := by
      apply Subtype.ext
      apply lp.ext
      funext x
      by_cases hx : x ∈ A <;>
        simp [BoundedMeasurableFunction.ofSimpleFunc_apply,
          BoundedMeasurableFunction.indicatorConst_apply, hx]
    rw [hfun, complexIntegral_indicatorConst,
      complexMeasureComponentCLM_apply,
      signedComplexIntegral_indicatorConst, signedComplexIntegral_indicatorConst]
    change c * mu A = c * ((mu A).re : ℂ) +
      Complex.I * (c * ((mu A).im : ℂ))
    calc
      c * mu A = c * ((mu A).re + (mu A).im * Complex.I) := by
        rw [Complex.re_add_im]
      _ = c * ((mu A).re : ℂ) + Complex.I * (c * ((mu A).im : ℂ)) := by ring
  · intro f g hdisj hf hg
    rw [ofSimpleFunc_add, complexIntegral_add, map_add, hf, hg]

omit [TopologicalSpace X] [R1Space X] [BorelSpace X] [CompactSpace X] [T2Space X] in
private theorem dense_range_ofSimpleFunc :
    Dense (Set.range (BoundedMeasurableFunction.ofSimpleFunc :
      SimpleFunc X ℂ → BoundedMeasurableFunction X)) := by
  rw [Metric.dense_iff]
  intro phi epsilon hepsilon
  obtain ⟨f, hf⟩ := BoundedMeasurableFunction.exists_simpleFunc_norm_sub_lt phi hepsilon
  refine ⟨BoundedMeasurableFunction.ofSimpleFunc f, ?_, ⟨f, rfl⟩⟩
  simpa [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm, norm_sub_rev] using hf

omit [TopologicalSpace X] [R1Space X] [BorelSpace X] [CompactSpace X] [T2Space X] in
private theorem complexIntegral_eq_component
    (mu : ComplexMeasure X) (phi : BoundedMeasurableFunction X) :
    complexIntegral mu phi = complexMeasureComponentCLM mu phi := by
  let : IsFiniteMeasure mu.variation := ComplexMeasure.isFiniteMeasure_variation mu
  have hmaps : complexIntegralCLM mu = complexMeasureComponentCLM mu := by
    apply ContinuousLinearMap.ext_on
      (dense_range_ofSimpleFunc (X := X) |>.mono Submodule.subset_span)
    rintro _ ⟨f, rfl⟩
    rw [complexIntegralCLM_apply]
    exact complexIntegral_eq_component_on_simple mu f
  exact congrArg (fun L : BoundedMeasurableFunction X →L[ℂ] ℂ ↦ L phi) hmaps

private noncomputable def continuousMapInclusionCLM :
    C(X, ℂ) →L[ℂ] BoundedMeasurableFunction X where
  toLinearMap :=
    (BoundedMeasurableFunction.continuousMapStarAlgHom (X := X)).toLinearMap
  cont := BoundedMeasurableFunction.isometry_continuousMapStarAlgHom.continuous

omit [R1Space X] [T2Space X] in
@[simp]
private theorem continuousMapInclusionCLM_apply (f : C(X, ℂ)) :
    continuousMapInclusionCLM f = BoundedMeasurableFunction.ofContinuousMap f := rfl

/-- Integration against a regular complex measure as a bounded complex
functional on `C(X, ℂ)`. -/
@[no_expose]
noncomputable def complexIntegralDual (mu : RegularComplexMeasure X) :
    StrongDual ℂ C(X, ℂ) := by
  let : IsFiniteMeasure (mu : ComplexMeasure X).variation :=
    ComplexMeasure.isFiniteMeasure_variation (mu : ComplexMeasure X)
  exact (complexIntegralCLM (mu : ComplexMeasure X)).comp continuousMapInclusionCLM

omit [T2Space X] in
/-- The continuous-function dual associated with a regular complex measure evaluates by complex
integration. -/
@[simp]
theorem complexIntegralDual_apply
    (mu : RegularComplexMeasure X) (f : C(X, ℂ)) :
    complexIntegralDual mu f =
      complexIntegral (mu : ComplexMeasure X)
        (BoundedMeasurableFunction.ofContinuousMap f) := by
  simp [complexIntegralDual]

omit [T2Space X] in
/-- The norm of the complex integral functional is bounded by the measure's total variation mass. -/
theorem norm_complexIntegralDual_le (mu : RegularComplexMeasure X) :
    ‖complexIntegralDual mu‖ ≤ (mu : ComplexMeasure X).variation.real univ := by
  let : IsFiniteMeasure (mu : ComplexMeasure X).variation :=
    ComplexMeasure.isFiniteMeasure_variation (mu : ComplexMeasure X)
  apply ContinuousLinearMap.opNorm_le_bound _ measureReal_nonneg
  intro f
  rw [complexIntegralDual_apply]
  calc
    ‖complexIntegral (mu : ComplexMeasure X)
        (BoundedMeasurableFunction.ofContinuousMap f)‖ ≤
        ‖BoundedMeasurableFunction.ofContinuousMap f‖ *
          (mu : ComplexMeasure X).variation.real univ :=
      norm_complexIntegral_le _ _
    _ = (mu : ComplexMeasure X).variation.real univ * ‖f‖ := by
      rw [show ‖BoundedMeasurableFunction.ofContinuousMap f‖ = ‖f‖ from
        BoundedMeasurableFunction.norm_continuousMapStarAlgHom f]
      ring

/-- Complex integration is linear in a regular complex measure. -/
noncomputable def regularComplexMeasureIntegral :
    RegularComplexMeasure X →ₗ[ℂ] StrongDual ℂ C(X, ℂ) where
  toFun := complexIntegralDual
  map_add' mu nu := by
    let : IsFiniteMeasure (mu : ComplexMeasure X).variation :=
      ComplexMeasure.isFiniteMeasure_variation (mu : ComplexMeasure X)
    let : IsFiniteMeasure (nu : ComplexMeasure X).variation :=
      ComplexMeasure.isFiniteMeasure_variation (nu : ComplexMeasure X)
    apply ContinuousLinearMap.ext
    intro f
    rw [complexIntegralDual_apply, add_apply, complexIntegralDual_apply,
      complexIntegralDual_apply]
    change complexIntegral ((mu : ComplexMeasure X) + (nu : ComplexMeasure X)) _ = _
    rw [complexIntegral_add_measure]
  map_smul' c mu := by
    apply ContinuousLinearMap.ext
    intro f
    rw [complexIntegralDual_apply, smul_apply, RingHom.id_apply, complexIntegralDual_apply]
    change complexIntegral (c • (mu : ComplexMeasure X)) _ =
      c • complexIntegral (mu : ComplexMeasure X) _
    rw [complexIntegral_smul_measure]

omit [T2Space X] in
/-- The linear map from regular complex measures evaluates through the complex integral functional. -/
@[simp]
theorem regularComplexMeasureIntegral_apply
    (mu : RegularComplexMeasure X) (f : C(X, ℂ)) :
    regularComplexMeasureIntegral mu f = complexIntegralDual mu f := by
  rfl

omit [T2Space X] in
private theorem signedComplexIntegral_ofReal
    (s : RegularSignedMeasure X) (f : C(X, ℝ)) :
    signedComplexIntegralCLM (s : SignedMeasure X)
        (BoundedMeasurableFunction.ofContinuousMap (realContinuousMapCLM f)) =
      (RegularSignedMeasure.signedIntegralDual s f : ℂ) := by
  let hs : (s : SignedMeasure X).Integrable (fun x ↦ f x) := by
    change Integrable (fun x ↦ f x) (s : SignedMeasure X).variation
    let : IsFiniteMeasure (s : SignedMeasure X).variation :=
      signedVariationFinite (s : SignedMeasure X)
    apply Integrable.of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖
    exact Filter.Eventually.of_forall fun x ↦ f.norm_coe_le_norm x
  rw [signedComplexIntegralCLM_apply, signedComplexIntegral,
    RegularSignedMeasure.signedIntegralDual_apply]
  let Br : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := (ContinuousLinearMap.lsmul ℝ ℝ).flip
  let Bc : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := (ContinuousLinearMap.lsmul ℝ ℝ).flip
  have hin := VectorMeasure.integral_continuousLinearMap_comp
    (μ := (s : SignedMeasure X)) (B := Bc) (C := Complex.ofRealCLM) hs
  have hout := VectorMeasure.continuousLinearMap_apply_integral
    (μ := (s : SignedMeasure X)) (B := Br) (C := Complex.ofRealCLM) hs
  have hpair : Bc ∘L Complex.ofRealCLM =
      (ContinuousLinearMap.compL ℝ ℝ ℝ ℂ Complex.ofRealCLM) ∘L Br := by
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro b
    simp [Bc, Br]
  have hmain :
      (∫ᵛ x, Complex.ofReal (f x) ∂[Bc; (s : SignedMeasure X)]) =
        Complex.ofReal (∫ᵛ x, f x ∂[Br; (s : SignedMeasure X)]) := calc
    _ = ∫ᵛ x, f x ∂[Bc ∘L Complex.ofRealCLM; (s : SignedMeasure X)] := hin
    _ = ∫ᵛ x, f x ∂[(ContinuousLinearMap.compL ℝ ℝ ℝ ℂ Complex.ofRealCLM) ∘L Br;
          (s : SignedMeasure X)] := by rw [hpair]
    _ = _ := hout.symm
  simpa only [BoundedMeasurableFunction.ofContinuousMap_apply,
    realContinuousMapCLM_apply] using hmain

omit [T2Space X] in
private theorem complexIntegralDual_restrictions
    (mu : RegularComplexMeasure X) :
    complexDualRealRestriction (complexIntegralDual mu) =
        RegularSignedMeasure.signedIntegralDual (RegularComplexMeasure.re mu) ∧
      complexDualImagRestriction (complexIntegralDual mu) =
        RegularSignedMeasure.signedIntegralDual (RegularComplexMeasure.im mu) := by
  constructor
  · apply ContinuousLinearMap.ext
    intro f
    have happ := complexIntegral_eq_component (mu : ComplexMeasure X)
      (BoundedMeasurableFunction.ofContinuousMap (realContinuousMapCLM f))
    rw [complexDualRealRestriction_apply, complexIntegralDual_apply]
    rw [happ, complexMeasureComponentCLM_apply,
      ← RegularComplexMeasure.coe_re, ← RegularComplexMeasure.coe_im,
      ← signedComplexIntegralCLM_apply, ← signedComplexIntegralCLM_apply,
      signedComplexIntegral_ofReal, signedComplexIntegral_ofReal]
    simp
  · apply ContinuousLinearMap.ext
    intro f
    have happ := complexIntegral_eq_component (mu : ComplexMeasure X)
      (BoundedMeasurableFunction.ofContinuousMap (realContinuousMapCLM f))
    rw [complexDualImagRestriction_apply, complexIntegralDual_apply]
    rw [happ, complexMeasureComponentCLM_apply,
      ← RegularComplexMeasure.coe_re, ← RegularComplexMeasure.coe_im,
      ← signedComplexIntegralCLM_apply, ← signedComplexIntegralCLM_apply,
      signedComplexIntegral_ofReal, signedComplexIntegral_ofReal]
    simp

/-- The regular complex measure representing a bounded complex functional. -/
noncomputable def complexRieszMeasure (Λ : StrongDual ℂ C(X, ℂ)) :
    RegularComplexMeasure X := by
  let s : RegularSignedMeasure X := signedRieszMeasure (complexDualRealRestriction Λ)
  let t : RegularSignedMeasure X := signedRieszMeasure (complexDualImagRestriction Λ)
  refine ⟨(s : SignedMeasure X).toComplexMeasure (t : SignedMeasure X), ?_⟩
  change VectorMeasure.HasRegularVariation
    ((s : SignedMeasure X).toComplexMeasure (t : SignedMeasure X))
  apply ComplexMeasure.hasRegularVariation_toComplexMeasure
  · rw [VectorMeasure.HasRegularVariation, ← SignedMeasure.totalVariation_eq_variation]
    exact RegularSignedMeasure.totalVariation_regular s
  · rw [VectorMeasure.HasRegularVariation, ← SignedMeasure.totalVariation_eq_variation]
    exact RegularSignedMeasure.totalVariation_regular t

/-- Integrating against the complex Riesz measure recovers the original continuous linear functional. -/
@[simp]
theorem complexIntegralDual_complexRieszMeasure (Λ : StrongDual ℂ C(X, ℂ)) :
    complexIntegralDual (complexRieszMeasure Λ) = Λ := by
  apply complexDual_eq_of_restrictions_eq
  · rw [(complexIntegralDual_restrictions (complexRieszMeasure Λ)).1]
    exact signedIntegralDual_signedRieszMeasure (complexDualRealRestriction Λ)
  · rw [(complexIntegralDual_restrictions (complexRieszMeasure Λ)).2]
    exact signedIntegralDual_signedRieszMeasure (complexDualImagRestriction Λ)

/-- A regular complex measure is determined by its integrals against continuous complex functions. -/
theorem complexIntegralDual_injective :
    Function.Injective (complexIntegralDual (X := X)) := by
  intro mu nu h
  have hre : RegularComplexMeasure.re mu = RegularComplexMeasure.re nu := by
    apply signedIntegralDual_injective
    rw [← (complexIntegralDual_restrictions mu).1,
      ← (complexIntegralDual_restrictions nu).1, h]
  have him : RegularComplexMeasure.im mu = RegularComplexMeasure.im nu := by
    apply signedIntegralDual_injective
    rw [← (complexIntegralDual_restrictions mu).2,
      ← (complexIntegralDual_restrictions nu).2, h]
  apply Subtype.ext
  calc
    (mu : ComplexMeasure X) =
        ((mu : ComplexMeasure X).re).toComplexMeasure ((mu : ComplexMeasure X).im) :=
      (ComplexMeasure.toComplexMeasure_to_signedMeasure _).symm
    _ = ((nu : ComplexMeasure X).re).toComplexMeasure ((nu : ComplexMeasure X).im) := by
      rw [← RegularComplexMeasure.coe_re, ← RegularComplexMeasure.coe_im,
        hre, him, RegularComplexMeasure.coe_re, RegularComplexMeasure.coe_im]
    _ = (nu : ComplexMeasure X) := ComplexMeasure.toComplexMeasure_to_signedMeasure _

/-- The complex Riesz construction recovers a regular complex measure from its integral functional. -/
@[simp]
theorem complexRieszMeasure_complexIntegralDual (mu : RegularComplexMeasure X) :
    complexRieszMeasure (complexIntegralDual mu) = mu := by
  apply complexIntegralDual_injective
  rw [complexIntegralDual_complexRieszMeasure]

/-- Complex Riesz--Markov as a complex-linear equivalence. -/
noncomputable def complexIntegralEquiv :
    RegularComplexMeasure X ≃ₗ[ℂ] StrongDual ℂ C(X, ℂ) where
  toLinearMap := regularComplexMeasureIntegral
  invFun := complexRieszMeasure
  left_inv := by
    intro mu
    change complexRieszMeasure (complexIntegralDual mu) = mu
    exact complexRieszMeasure_complexIntegralDual mu
  right_inv := by
    intro Λ
    change complexIntegralDual (complexRieszMeasure Λ) = Λ
    exact complexIntegralDual_complexRieszMeasure Λ

/-- The complex Riesz equivalence sends a measure to its integral functional. -/
@[simp]
theorem complexIntegralEquiv_apply (mu : RegularComplexMeasure X) :
    complexIntegralEquiv mu = complexIntegralDual mu := by
  rfl

/-- The inverse complex Riesz equivalence is the constructed representing measure. -/
@[simp]
theorem complexIntegralEquiv_symm_apply (Λ : StrongDual ℂ C(X, ℂ)) :
    (complexIntegralEquiv (X := X)).symm Λ = complexRieszMeasure Λ := by
  rfl

/-- The complex Riesz representing measure commutes with complex scalar multiplication. -/
@[simp]
theorem complexRieszMeasure_smul (c : ℂ) (Λ : StrongDual ℂ C(X, ℂ)) :
    complexRieszMeasure (c • Λ) = c • complexRieszMeasure Λ := by
  simpa only [complexIntegralEquiv_symm_apply] using
    (complexIntegralEquiv (X := X)).symm.map_smul c Λ

/-- A finite bound for the actual Riesz measure's Borel integral, needed to construct bounded operator coefficients. -/
theorem norm_complexIntegral_complexRieszMeasure_le_two
    (Λ : StrongDual ℂ C(X, ℂ)) (phi : BoundedMeasurableFunction X) :
    ‖complexIntegral (complexRieszMeasure Λ : ComplexMeasure X) phi‖ ≤ 2 * ‖Λ‖ * ‖phi‖ := by
  let s : RegularSignedMeasure X := signedRieszMeasure (complexDualRealRestriction Λ)
  let t : RegularSignedMeasure X := signedRieszMeasure (complexDualImagRestriction Λ)
  have hmeasure : (complexRieszMeasure Λ : ComplexMeasure X) =
      (s : SignedMeasure X).toComplexMeasure (t : SignedMeasure X) := rfl
  rw [hmeasure, complexIntegral_eq_component, complexMeasureComponentCLM_apply,
    SignedMeasure.re_toComplexMeasure, SignedMeasure.im_toComplexMeasure]
  calc
    ‖signedComplexIntegral (s : SignedMeasure X) phi +
        Complex.I * signedComplexIntegral (t : SignedMeasure X) phi‖ ≤
        ‖signedComplexIntegral (s : SignedMeasure X) phi‖ +
          ‖Complex.I * signedComplexIntegral (t : SignedMeasure X) phi‖ := norm_add_le _ _
    _ = ‖signedComplexIntegral (s : SignedMeasure X) phi‖ +
        ‖signedComplexIntegral (t : SignedMeasure X) phi‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ ‖phi‖ * (s : SignedMeasure X).totalVariation.real univ +
        ‖phi‖ * (t : SignedMeasure X).totalVariation.real univ :=
      add_le_add (norm_signedComplexIntegral_le (s : SignedMeasure X) phi)
        (norm_signedComplexIntegral_le (t : SignedMeasure X) phi)
    _ = ‖phi‖ * ‖complexDualRealRestriction Λ‖ + ‖phi‖ * ‖complexDualImagRestriction Λ‖ := by
      rw [show (s : SignedMeasure X).totalVariation.real univ = ‖complexDualRealRestriction Λ‖ from
          totalVariation_signedRieszMeasure _,
        show (t : SignedMeasure X).totalVariation.real univ = ‖complexDualImagRestriction Λ‖ from
          totalVariation_signedRieszMeasure _]
    _ ≤ ‖phi‖ * ‖Λ‖ + ‖phi‖ * ‖Λ‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (norm_complexDualRealRestriction_le Λ) (norm_nonneg phi))
        (mul_le_mul_of_nonneg_left (norm_complexDualImagRestriction_le Λ) (norm_nonneg phi))
    _ = 2 * ‖Λ‖ * ‖phi‖ := by ring

end

end MathlibExt.MeasureTheory
